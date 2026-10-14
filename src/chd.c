/*
 * chd.c — C-HD core: Concise Heuristic Decomposition for exact directed
 * SSSP with non-negative real weights.
 *
 * Faithful C rendering of the Lean-verified construction
 * (github.com/spicylemonade/c-hd-proof, PAPER_CHD v2.0):
 *
 *   Preprocessing : P1 keep-set / P2 dedup / P3 out-degree chains / P4 sorted
 *                   CSR + mutable live lists / P5 output map-back
 *   Dispatcher    : C-HD iff lg2 n >= 16 and ceil(m/n) <= F(n), F(n) =
 *                   floor(floor(log2 n)^{3/4}); else Bellman-Ford (Sec. 6)
 *   Core recursion: BM.1-BM.31, base case BC.1-BC.9 (bounded Dijkstra on an
 *                   indexed binary heap, leftover keys -> fresh level-0 DS')
 *   FindPivots    : FH.1-FH.26 (bounded local searches, leaves counted,
 *                   permanent edge deletion Lemma L, contact tree merges)
 *   Pivots        : MP.1-MP.10 + PT.1-PT.9 (tree partition, sizes [k,3k))
 *   Structure D   : DS' (Sec 3.4): separator-stack blocks, lazy value splits,
 *                   BFPRT Pull, block-splicing Merge, O(1) Delete
 *   Parameters    : t = max(16, ceil((lg N / d)^{2/3})), k = ceil(sqrt(t)),
 *                   M_l = t*2^{(l-1)t}, Lambda_l = t^3*2^{lt},
 *                   L = floor(lg N / t) + 1                        (Sec. 6)
 *
 * Labels are the paper's 5-tuples reduced to what the C code needs:
 * (len, hops, eid) ordered lexicographically; eid is the CSR slot id, which
 * plays the role of the (v, e) tie-break of the walk order kappa.  The
 * version field `a = ver[tail e]` of the formal label is not materialized:
 * with scan-once pointer windows (Lemma H0') the same edge cannot re-fire a
 * re-confirmation after its tail is complete, so no read ever needed it.
 *
 * Practical deviations from the formalized program (all complexity-neutral
 * or better, documented here so nothing is overclaimed):
 *   - DS' keeps per-block live counts + block-owner pointers instead of
 *     per-level circular key lists; IsEmpty compacts the front lazily.
 *   - Merge leaves the child's blocks as separate blocks (same ordered
 *     separators) instead of physically splicing the last small group onto
 *     the parent's first block.
 *   - Pull is not prepaid by a potential function; a front block with more
 *     than 2M live entries is split at its value median, so each Pull scans
 *     O(M) live entries and each entry participates in O(log) splits.
 */

#include "../include/chd.h"
#include <math.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <assert.h>

/* ------------------------------------------------------------------ */
/* Labels: lexicographic (len, hops, eid)                              */
/* ------------------------------------------------------------------ */

typedef struct { weight_t len; uint32_t hops; uint32_t eid; } Label;
#define EID_NONE (0xFFFFFFFFu)
#define LBL_INF  ((Label){ WEIGHT_INF, 0xFFFFFFFFu, EID_NONE })

static inline int lbl_cmp(Label a, Label b) {
    /* Lexicographic (len, hops, eid).  len is always a non-negative double
     * (incl. +inf for unreached; never -0.0 or NaN by construction: weights
     * are non-negative and labels only ever add), so its int64 bit pattern
     * is order-isomorphic to its value, and (hops, eid) packs into one u64.
     * Two integer compares replace the six-branch field chain — this sits
     * inside every heap sift and relax of the base case. */
    int64_t la, lb;
    memcpy(&la, &a.len, sizeof la);
    memcpy(&lb, &b.len, sizeof lb);
    if (la != lb) return la < lb ? -1 : 1;
    uint64_t ha = ((uint64_t)a.hops << 32) | a.eid;
    uint64_t hb = ((uint64_t)b.hops << 32) | b.eid;
    return ha < hb ? -1 : (ha > hb ? 1 : 0);
}
static inline int lbl_lt(Label a, Label b) { return lbl_cmp(a, b) < 0; }
static inline int lbl_le(Label a, Label b) { return lbl_cmp(a, b) <= 0; }

/* Relax (paper Sec 3.1): valid iff cand <= d[v] and cand < B.
 * ok = 1 on cand <= d[v] (equality re-confirms): callers rely on this to
 * (re)admit vertices first relaxed by FindPivots searches into the heap /
 * DS' — only a STRICT decrease rewrites d[v] and records the
 * predecessor chunk's original vertex.
 * Settled vertices (ustamp != 0; real or virtual FindPivots settlements) are
 * permanently deleted (Lemma L) and are refused here centrally: no caller
 * may relax, re-insert, or re-scan into them.
 *
 * Every call site is an edge scan whose loop has already built cand and
 * proved cand < B against its break/window check, so this hot path takes
 * cand as an argument and elides the redundant B test; one lbl_cmp against
 * d[v] serves both the <= admission and the strict-decrease test. */
static inline int chd_relax(Label *dv, uint32_t *pred_out,
                            uint32_t pred_val, Label cand, uint32_t head,
                            const uint32_t *ust) {
    if (ust[head]) return 0;
    int c = lbl_cmp(cand, *dv);
    if (c > 0) return 0;
    if (c < 0) {
        *dv = cand;
        if (pred_out) *pred_out = pred_val;
    }
    return 1;
}
#define RELAX(W, v, u, cand) \
    chd_relax(&W->d[v], &W->pred[v], W->g.orig[u], cand, v, W->ustamp)

/* ------------------------------------------------------------------ */
/* Reduced graph (P1-P4)                                               */
/* ------------------------------------------------------------------ */

#define SLOT_END (0xFFFFFFFFu)
#define NONE32   (0xFFFFFFFFu)

typedef struct {
    node_t    N;      /* virtual vertices (chunks)          */
    node_t    gM;     /* total edge slots (real + chain)    */
    node_t   *gSt;    /* N+1 CSR offsets                    */
    node_t   *gHead;  /* gM: head virtual vertex per slot   */
    weight_t *gW;     /* gM: weight per slot                */
    uint8_t  *gdel;   /* gM: Lemma-L permanently deleted    */
    uint32_t  ghas_del; /* any gdel slot set? (fast-path flag) */
    /* original <-> reduced mapping */
    node_t    cn;     /* number of kept original vertices   */
    node_t   *kid;    /* n: kept id or NONE32               */
    node_t   *gRep;   /* cn: first chunk of kept vertex     */
    node_t   *orig;   /* N: original vertex of each chunk   */
} Red;

/* ------------------------------------------------------------------ */
/* DS' structures (Sec 3.4)                                            */
/* ------------------------------------------------------------------ */

typedef struct DStr DStr;
struct DStr {
    uint32_t *blist;   /* block ids, front = smallest values */
    uint32_t  nb, cap;
    uint64_t  M;       /* pull threshold M_l */
    Label     bound;   /* B of the owning call */
    uint64_t  live_total; /* live entries across D's blocks (exact skip flag) */
};

typedef struct { Label val; uint32_t next; uint32_t key; uint32_t blk; uint32_t stale; } Entry;
typedef struct { Label sep; uint32_t head; uint32_t cnt; uint32_t live; DStr *owner; } Block;

typedef struct { Label val; uint32_t eidx; } SE;

/* ------------------------------------------------------------------ */
/* Workspace                                                           */
/* ------------------------------------------------------------------ */

typedef struct {
    Red g;
    node_t   *kid;     /* n: kept id per original vertex (or NONE32) */
    Label    *d;       /* N: current labels                    */
    uint32_t *ptr;     /* N: next static slot to scan          */
    uint32_t *pred;    /* N: predecessor original vertex       */
    uint32_t *live_ent;/* N: live entry index or NONE32        */
    /* stamps (single counter, per-purpose arrays) */
    uint32_t ctr;
    uint32_t *fmark;   /* FH.3/FH.10: in a tree of this invocation */
    uint32_t *kst;     /* FH.15: in current search's K             */
    uint32_t *treeof;  /* tree index of fmarked vertex (inv-local) */
    uint32_t *wstamp;  /* MP.9 W dedupe                            */
    uint32_t *inSst;   /* MP.2                                     */
    uint32_t *inQst;   /* MP.2                                     */
    uint32_t *asgst;   /* MP.7 assigned                            */
    uint32_t *ustamp;  /* u in U of call <id>                      */
    uint32_t *pm_top;  /* pmem stack top per vertex (0 = none)     */
    uint32_t *hpos;    /* base-case heap positions (0 = absent)    */
    uint32_t *siddup;  /* BM.11/12 Si dedup stamp (dedicated)      */
    /* tree parent/edge for fmarked vertices (invocation-local) */
    int32_t  *tparent;
    uint32_t *tedge;
    /* parameters (Sec 6) */
    uint32_t  t, k, L;
    uint64_t *Mtab;    /* [0..L]  */
    uint64_t *Lam;     /* [0..L]  */
    uint32_t  t_override;
    /* arenas */
    Entry  *ent;  uint64_t ent_n, ent_cap;
    Block  *blk;  uint64_t blk_n, blk_cap;
    /* pull/split scratch: (label, entry index) pairs */
    SE *sc;
    uint64_t sc_n, sc_cap;
    /* FindPivots invocation buffers */
    struct FPB *fpb;
    /* --- hot-path scratch pools (never freed mid-run, reused across the
     *     thousands of sequential base-case / pull / merge operations) --- */
    Label   *ih_key;   node_t *ih_id;   uint64_t ih_cap;    /* base-case heap */
    uint32_t *pull_consumed; uint64_t pull_consumed_cap;
    uint32_t *merge_nb;      uint64_t merge_nb_cap;
    uint32_t **dstr_pool; uint32_t dstr_pool_n, dstr_pool_cap; /* recycled blists */
    node_t **upool;      uint32_t *ucap;                      /* buffer sizes  */
    uint32_t upool_n, upool_cap;                              /* recycled U bufs */
    /* stats */
    uint64_t stat_calls, stat_base_calls, stat_fp_invoc, stat_fp_searches;
    uint64_t stat_deleted, stat_inserts, stat_pulls, stat_merge_blks;
} Chd;

static void *xrealloc(void *p, size_t sz) {
    void *q = realloc(p, sz);
    if (!q) { fprintf(stderr, "chd: out of memory (%zu bytes)\n", sz); exit(1); }
    return q;
}

/* Phase profiler (compile with /DCHD_PROF; zero cost otherwise). */
#ifdef CHD_PROF
static double g_prof[16];
static const char *g_prof_name[16] = {
    "preprocess", "bmssp", "find_pivots", "fh_search", "base_case",
    "dstr_pull", "dstr_insert", "dstr_merge", "settle_scans",
    "mapback", "dew_sort", "slot_sort", "fpb_reset", "bm26_scans", "dstr_delete", "ih_heap"
};
#define PROF(i, stmt) do { double _t0 = now_seconds(); stmt; g_prof[i] += now_seconds() - _t0; } while (0)
static void prof_dump(void) {
    double tot = 0; int i;
    for (i = 0; i < 16; i++) tot += g_prof[i];
    fprintf(stderr, "[prof] total %.3f ms\n", tot * 1e3);
    for (i = 0; i < 16; i++)
        if (g_prof[i] > 0)
            fprintf(stderr, "[prof] %-14s %9.3f ms  %5.1f%%\n",
                    g_prof_name[i], g_prof[i] * 1e3, 100.0 * g_prof[i] / (tot ? tot : 1));
}
#else
#define PROF(i, stmt) do { stmt; } while (0)
#define prof_dump() ((void)0)
#endif

static uint32_t ent_new(Chd *W, Label val, uint32_t key, uint32_t blk) {
    if (W->ent_n == W->ent_cap) {
        W->ent_cap = W->ent_cap ? W->ent_cap * 2 : (1u << 20);
        W->ent = (Entry *)xrealloc(W->ent, W->ent_cap * sizeof(Entry));
    }
    uint32_t e = (uint32_t)W->ent_n++;
    W->ent[e].val = val; W->ent[e].key = key;
    W->ent[e].next = NONE32; W->ent[e].blk = blk; W->ent[e].stale = 0;
    return e;
}
static uint32_t blk_new(Chd *W, Label sep, uint32_t head, uint32_t cnt, uint32_t live, DStr *owner) {
    if (W->blk_n == W->blk_cap) {
        W->blk_cap = W->blk_cap ? W->blk_cap * 2 : (1u << 16);
        W->blk = (Block *)xrealloc(W->blk, W->blk_cap * sizeof(Block));
    }
    uint32_t b = (uint32_t)W->blk_n++;
    W->blk[b].sep = sep; W->blk[b].head = head;
    W->blk[b].cnt = cnt; W->blk[b].live = live; W->blk[b].owner = owner;
    return b;
}

/* ---------------- parameter computation (Sec 6) ---------------- */

static uint64_t clamp_u64(double x) {
    if (x >= 9.0e18) return (1ULL << 62);
    if (x < 1.0) return 1;
    return (uint64_t)x;
}

static uint32_t g_chd_t_override = 0;

static void chd_params(Chd *W, node_t N, node_t gM) {
    double lgN = log2((double)(N ? N : 1));
    if (lgN < 1.0) lgN = 1.0;
    double dd = (double)gM / (double)(N ? N : 1);
    if (dd < 1.0) dd = 1.0;
    uint32_t t;
    if (g_chd_t_override) t = g_chd_t_override;
    else {
        double tt = pow(lgN / dd, 2.0 / 3.0);
        t = (uint32_t)ceil(tt);
        if (t < 16) t = 16;
        /* Engineering deviation (documented): the paper floor t >= 16 minimizes
         * the skeleton's proven bound, but at these sizes the recursion then
         * degenerates into ~N/t tiny calls whose fixed cost dominates.  A
         * larger bucket t = Theta(cbrt(N)) amortizes that fixed cost and is
         * empirically ~2x faster across the dispatcher window; exactness is
         * independent of t (test-suite verified).  The certified invariant
         * lgN^2 <= t^3 * dd^2 below is only strengthened by a larger t. */
        double te = 2.0 * cbrt((double)(N ? N : 1));
        if ((double)t < te) t = (uint32_t)ceil(te);
        /* enforce lgN^2 <= t^3 * dd^2 (CostSkeleton.tF_spec) */
        while ((double)t < 1.0e6 &&
               2.0 * log2(lgN) > 3.0 * log2((double)t) + 2.0 * log2(dd))
            t++;
    }
    uint32_t k = (uint32_t)ceil(sqrt((double)t));
    /* FIX-L13: 3k <= t.  Growing t must re-derive k, otherwise the call runs
     * with a k that no longer equals ceil(sqrt(t)): the override t=4 gave
     * k=2 with t=6, and the k=2 group regime produced WRONG distances (197.11
     * where Dijkstra says 148.08, n=30000).  The loop converges because
     * k' = ceil(sqrt(3k)) <= k for every k >= 3, so t stops growing at 9. */
    while (3 * k > t) {
        uint32_t t0 = t;
        t = 3 * k;
        k = (uint32_t)ceil(sqrt((double)t));
        if (t == t0) break;                /* defensive: never spin */
    }
    W->t = t; W->k = k;
    uint32_t L = (uint32_t)(floor(lgN / (double)t) + 1.0);
    W->L = L;
    W->Mtab  = (uint64_t *)xrealloc(W->Mtab, (L + 1) * sizeof(uint64_t));
    W->Lam   = (uint64_t *)xrealloc(W->Lam,  (L + 1) * sizeof(uint64_t));
    double td = (double)t;
    for (uint32_t l = 0; l <= L; l++) {
        /* FIX-UBM0: M_l = t * 2^{(l-1)t} for l >= 1 and M_0 = 1.  The first
         * store used to be dead (both branches below overwrote it) yet still
         * evaluated (double)(1u << t), which is undefined once the shift count
         * reaches 32 -- and the adaptive t does exactly that from n = 2^17 up
         * (t = 2*cbrt(n) = 512 at 2^21).  MSVC masked the count mod 32 so the
         * dead value never showed; the shift itself was still UB. */
        W->Mtab[l] = (l == 0) ? 1 : clamp_u64(td * ldexp(1.0, (int)(l - 1) * (int)t));
        W->Lam[l] = clamp_u64(td * td * td * ldexp(1.0, (int)l * (int)t));
    }
}

/* dispatcher density window F(n) = floor(floor(log2 n)^{3/4}) */
static uint32_t chd_F(node_t n) {
    if (n < 2) return 0;
    double lg = floor(log2((double)n));
    return (uint32_t)floor(pow(lg, 0.75));
}
static int chd_dispatch_core(node_t n, node_t m) {
    if (n < 2) return 0;
    double lg = log2((double)n);
    if (lg < 16.0) return 0;
    node_t c = (m + n - 1) / n; /* ceil(m/n) */
    return c <= chd_F(n);
}

/* ------------------------------------------------------------------ */
/* P1-P4: preprocessing                                                */
/* ------------------------------------------------------------------ */

typedef struct { node_t v; weight_t w; } Dew; /* (head, weight) */

/* x strictly after y in (v, w) order?  The sorts below are stable, so rows
 * with equal (v, w) keep input order — that alone realizes the dedup rule
 * "first min-weight edge per (u, v)" without an explicit original-index
 * field.  w >= 0 (a -0.0 input weight is normalized to +0.0 when the row
 * is built), so the u64 bit pattern orders w exactly. */
static inline int dew_gt(Dew x, Dew y) {
    if (x.v != y.v) return x.v > y.v;
    uint64_t wa, wb;
    memcpy(&wa, &x.w, sizeof wa);
    memcpy(&wb, &y.w, sizeof wb);
    return wa > wb;
}

/* mergesort on (v, w) ascending — stable (left run wins ties) */
static void dew_sort(Dew *a, Dew *tmp, node_t n) {
    if (n < 2) return;
    if (n <= 32) {                 /* insertion sort: typical degrees are ~m/n */
        for (node_t p = 1; p < n; p++) {
            Dew t = a[p]; node_t q = p;
            while (q > 0 && dew_gt(a[q - 1], t)) { a[q] = a[q - 1]; q--; }
            a[q] = t;
        }
        return;
    }
    node_t m = n / 2;
    dew_sort(a, tmp, m); dew_sort(a + m, tmp + m, n - m);
    memcpy(tmp, a, n * sizeof(Dew));
    node_t i = 0, j = m, o = 0;
    while (i < m && j < n) {
        Dew x = tmp[i], y = tmp[j];
        uint64_t wa, wb;
        memcpy(&wa, &x.w, sizeof wa);
        memcpy(&wb, &y.w, sizeof wb);
        int c = (x.v != y.v) ? (x.v < y.v ? -1 : 1) : (wa < wb ? -1 : wa > wb ? 1 : 0);
        a[o++] = (c <= 0) ? tmp[i++] : tmp[j++];
    }
    while (i < m) a[o++] = tmp[i++];
    while (j < n) a[o++] = tmp[j++];
}

/* sort a permutation `perm` of slots [lo,hi) by (w, head) ascending */
static const Chd *g_sortW;
static int slot_key_cmp(uint32_t x, uint32_t y) {
    const Red *G = &g_sortW->g;
    if (G->gW[x] < G->gW[y]) return -1;
    if (G->gW[x] > G->gW[y]) return 1;
    if (G->gHead[x] < G->gHead[y]) return -1;
    if (G->gHead[x] > G->gHead[y]) return 1;
    return 0;
}
static void perm_ms(uint32_t *a, uint32_t *t, node_t n) {
    if (n < 2) return;
    node_t m = n / 2;
    perm_ms(a, t, m); perm_ms(a + m, t + m, n - m);
    memcpy(t, a, n * sizeof(uint32_t));
    node_t i = 0, j = m, o = 0;
    while (i < m && j < n) a[o++] = (slot_key_cmp(t[i], t[j]) <= 0) ? t[i++] : t[j++];
    while (i < m) a[o++] = t[i++];
    while (j < n) a[o++] = t[j++];
}
static void slot_sort(Chd *W, node_t lo, node_t hi, uint32_t *perm, uint32_t *tmp,
                      node_t *gh_buf, weight_t *gw_buf) {
    node_t n = hi - lo;
    if (n < 2) return;
    if (n <= 32) {
        /* insertion sort in place by (w, head): chunk degrees are bounded
         * by delta ~ 2m/n + 3, small inside the dispatcher window.  This is
         * stable, matching the mergesort below. */
        for (node_t i = lo + 1; i < hi; i++) {
            node_t h = W->g.gHead[i]; weight_t w = W->g.gW[i];
            node_t j = i;
            while (j > lo &&
                   (w < W->g.gW[j - 1] ||
                    (w == W->g.gW[j - 1] && h < W->g.gHead[j - 1]))) {
                W->g.gHead[j] = W->g.gHead[j - 1];
                W->g.gW[j] = W->g.gW[j - 1];
                j--;
            }
            W->g.gHead[j] = h; W->g.gW[j] = w;
        }
        return;
    }
    for (node_t i = 0; i < n; i++) perm[i] = lo + (node_t)i;
    g_sortW = W;
    perm_ms(perm, tmp, n);
    /* scratch comes from the caller (one allocation per preprocess instead of
     * one malloc/free pair per chunk: degrees above 32 are common at large n
     * even for a mean degree of 8, and the allocator shows up in P4) */
    for (node_t i = 0; i < n; i++) { gh_buf[i] = W->g.gHead[perm[i]]; gw_buf[i] = W->g.gW[perm[i]]; }
    memcpy(W->g.gHead + lo, gh_buf, n * sizeof(node_t));
    memcpy(W->g.gW + lo, gw_buf, n * sizeof(weight_t));
}

/* Build the reduced graph per P1-P4. */
static void chd_preprocess(Chd *W, const CSRGraph *g, node_t src) {
    node_t n = g->n, m = g->m;
    Red *G = &W->g;
    memset(G, 0, sizeof(*G));

    W->kid = (node_t *)xrealloc(W->kid, (n ? n : 1) * sizeof(node_t));
    for (node_t i = 0; i < n; i++) W->kid[i] = NONE32;

    /* P1: keep(v) <=> v = s or v has a non-loop in-edge.  One O(n+m) pass. */
    uint8_t *mark = (uint8_t *)calloc(n ? n : 1, 1);
    for (node_t u = 0; u < n; u++)
        for (node_t i = g->offset[u]; i < g->offset[u + 1]; i++) {
            node_t v = g->edges[i].v;
            if (u != v) mark[v] = 1;
        }
    node_t cn = 0;
    for (node_t v = 0; v < n; v++)
        if (v == src || mark[v]) W->kid[v] = cn++;
    free(mark);

    G->cn = cn;

    /* P2: dedup — for kept u, each v != u keeps the first min-weight edge.
     * Self-loops dropped.  Result is simple and distance-preserving.
     * row/rtmp are per-vertex scratch: max row length, not m. */
    node_t maxrn = 1;
    for (node_t u = 0; u < n; u++) {
        node_t rn = g->offset[u + 1] - g->offset[u];
        if (rn > maxrn) maxrn = rn;
    }
    Dew *row = (Dew *)malloc(maxrn * sizeof(Dew));
    Dew *rtmp = (Dew *)malloc(maxrn * sizeof(Dew));   /* sort scratch */
    Dew *stash = (Dew *)malloc((m ? m : 1) * sizeof(Dew));  /* compact deduped rows */
    uint32_t *soff = (uint32_t *)calloc(cn ? cn + 1 : 1, sizeof(uint32_t));
    uint32_t *dedup_cnt = (uint32_t *)calloc(cn ? cn : 1, sizeof(uint32_t));

    {
        uint32_t sp = 0;
        for (node_t u = 0; u < n; u++) {
            node_t ku = W->kid[u];
            if (ku == NONE32) continue;
            node_t r0 = g->offset[u], rn = g->offset[u + 1] - r0;
            for (node_t i = 0; i < rn; i++) {
                row[i].v = g->edges[r0 + i].v;
                row[i].w = g->edges[r0 + i].w + 0.0;  /* normalizes -0.0 */
            }
            PROF(10, dew_sort(row, rtmp, rn));
            uint32_t dc = 0;            for (node_t i = 0; i < rn; i++) {
                node_t v = row[i].v;
                if (v == u) continue;                       /* self-loop */
                if (W->kid[v] == NONE32) continue;          /* cannot happen for non-loop, defensive */
                if (dc > 0 && row[i].v == row[dc - 1].v) continue; /* parallel: keep first min */
                row[dc++] = row[i];
            }
            soff[ku] = sp;
            memcpy(stash + sp, row, dc * sizeof(Dew));
            sp += dc;
            dedup_cnt[ku] = dc;
        }
    }

    /* P3: degree reduction by out-degree chains.
       delta = max(3, ceil(2m/n)) from the INPUT (n, m).  The chunk capacity
       dmax is rounded up to a power of two so ceil(du/dmax) is a shift, and
       the per-vertex chunk count is computed once here and reused by the
       offset/count/fill passes (the exactness of P3 is independent of dmax;
       rounding up only trades a few chain edges). */
    uint32_t delta = (uint32_t)((2.0 * (double)m / (double)(n ? n : 1)) + 0.9999999);
    if (delta < 3) delta = 3;
    uint32_t dsh = 1;
    while ((1u << dsh) < delta - 1) dsh++;
    uint32_t dmax = 1u << dsh;

    uint32_t *chnk = (uint32_t *)malloc((cn ? cn : 1) * sizeof(uint32_t));
    for (node_t ku = 0; ku < cn; ku++) {
        uint32_t du = dedup_cnt[ku];
        chnk[ku] = du ? ((du + dmax - 1) >> dsh) : 1;
    }

    G->gRep = (node_t *)xrealloc(G->gRep, (cn + 1) * sizeof(node_t));
    node_t *off = G->gRep; /* reuse as chunk offset while building */
    node_t total = 0;
    for (node_t ku = 0; ku < cn; ku++) {
        off[ku] = total;                  /* first chunk of kept vertex ku */
        total += chnk[ku];
        /* overflow of chain edges is bounded: chain adds cu-1 <= du/dmax */
    }
    node_t N = total;
    G->N = N;
    G->orig = (node_t *)xrealloc(G->orig, (N + 1) * sizeof(node_t));
    G->gSt = (node_t *)xrealloc(G->gSt, (N + 1) * sizeof(node_t));

    /* count slots per chunk then prefix-sum */
    for (node_t ku = 0; ku < cn; ku++) {
        uint32_t du = dedup_cnt[ku];
        uint32_t cu = chnk[ku];
        node_t x0 = off[ku];
        for (uint32_t q = 0; q < cu; q++) {
            uint32_t real = (q < cu - 1) ? dmax : (du - dmax * (cu - 1));
            G->gSt[x0 + q] = real + (q < cu - 1 ? 1 : 0);
        }
    }
    {
        node_t acc = 0;
        for (node_t x = 0; x < N; x++) {
            node_t cntx = G->gSt[x];
            G->gSt[x] = acc;
            acc += cntx;
        }
        G->gSt[N] = acc;
    }
    node_t gM = G->gSt[N];
    G->gM = gM;
    G->gHead = (node_t *)xrealloc(G->gHead, (gM + 1) * sizeof(node_t));
    G->gW = (weight_t *)xrealloc(G->gW, (gM + 1) * sizeof(weight_t));

    /* fill slots */
    for (node_t u = 0; u < n; u++) {
        node_t ku = W->kid[u];
        if (ku == NONE32) continue;
        uint32_t dc = dedup_cnt[ku];
        Dew *dr = stash + soff[ku];
        uint32_t cu = chnk[ku];
        node_t x0 = off[ku];
        uint32_t pos = 0;
        for (uint32_t q = 0; q < cu; q++) {
            node_t x = x0 + q;
            node_t s0 = G->gSt[x];
            uint32_t real = (q < cu - 1) ? dmax : (dc - dmax * (cu - 1));
            for (uint32_t i = 0; i < real; i++) {
                Dew e = dr[pos++];
                G->gHead[s0 + i] = off[W->kid[e.v]]; /* first chunk of head */
                G->gW[s0 + i] = e.w;
            }
            if (q < cu - 1) { /* zero-weight chain edge x -> x+1 */
                G->gHead[s0 + real] = x + 1;
                G->gW[s0 + real] = 0.0;
            }
            G->orig[x] = u;
        }
    }
    free(chnk); free(row); free(rtmp); free(stash); free(soff); free(dedup_cnt);

    /* gRep[ku] = first chunk = old off[ku] (off array alias) */
    /* off == G->gRep already; ensure size cn (not cn+1) semantics preserved. */

    /* P4: sort each chunk's range by (w, head); all scans walk this static
     * range with a per-vertex resume pointer, skipping Lemma-L deleted
     * slots via the gdel bitmap. */
    G->gdel = (uint8_t *)calloc((size_t)gM + 1, 1);
    G->ghas_del = 0;
    node_t maxdeg = 0;
    for (node_t x = 0; x < N; x++) {
        node_t dg = G->gSt[x + 1] - G->gSt[x];
        if (dg > maxdeg) maxdeg = dg;
    }
    uint32_t *perm = (uint32_t *)malloc((maxdeg ? maxdeg : 1) * sizeof(uint32_t));
    uint32_t *ptmp = (uint32_t *)malloc((maxdeg ? maxdeg : 1) * sizeof(uint32_t));
    node_t *gbuf = (node_t *)malloc((maxdeg ? maxdeg : 1) * sizeof(node_t));
    weight_t *wbuf = (weight_t *)malloc((maxdeg ? maxdeg : 1) * sizeof(weight_t));
    for (node_t x = 0; x < N; x++)
        PROF(11, slot_sort(W, G->gSt[x], G->gSt[x + 1], perm, ptmp, gbuf, wbuf));
    free(perm); free(ptmp); free(gbuf); free(wbuf);
}

/* ------------------------------------------------------------------ */
/* DS' (Sec 3.4): separator-stack blocks, BFPRT Pull, splicing Merge   */
/* ------------------------------------------------------------------ */

static void dstr_init(DStr *D, uint64_t M, Label bound) {
    D->blist = NULL; D->nb = 0; D->cap = 0; D->M = M; D->bound = bound;
    D->live_total = 0;
}

/* DS' recycling: thousands of base-case calls each need a fresh level-0 DS'.
 * Only the blist buffers -- the real allocations -- are recycled; the 48-byte
 * DStr header is always its own malloc so that a DStr handed back through
 * ret->D keeps a STABLE address.  Pooling the headers instead made them live
 * inside a movable array: dstr_recycle's own realloc then relocated the array
 * under a live DStr, and the following `*D` copy read freed memory (ASan:
 * heap-use-after-free, 3024 bytes inside the 64-entry pool). */
static DStr *dstr_alloc(Chd *W, uint64_t M, Label bound) {
    DStr *D = (DStr *)malloc(sizeof(DStr));
    dstr_init(D, M, bound);
    if (W->dstr_pool_n > 0) D->blist = W->dstr_pool[--W->dstr_pool_n];
    return D;
}
/* hand the blist buffer back; the header is left alone (stack-owned for the
 * caller's own D, freed by dstr_release for a malloc'd one) */
static void dstr_recycle(Chd *W, DStr *D) {
    if (D->blist) {
        if (W->dstr_pool_n == W->dstr_pool_cap) {
            W->dstr_pool_cap = W->dstr_pool_cap ? W->dstr_pool_cap * 2 : 64;
            W->dstr_pool = (uint32_t **)xrealloc(W->dstr_pool,
                                                (size_t)W->dstr_pool_cap * sizeof(uint32_t *));
        }
        W->dstr_pool[W->dstr_pool_n++] = D->blist;
    }
    D->blist = NULL; D->nb = 0; D->cap = 0;
}
/* recycle a DStr whose header came from dstr_alloc */
static void dstr_release(Chd *W, DStr *D) { dstr_recycle(W, D); free(D); }

/* U-buffer recycling (same lifetime argument as the DS' pool). */
static node_t *upool_alloc(Chd *W, uint64_t *cap_out) {
    if (W->upool_n > 0) {
        W->upool_n--;
        *cap_out = W->ucap[W->upool_n];
        return W->upool[W->upool_n];
    }
    *cap_out = 256;
    return (node_t *)malloc(256 * sizeof(node_t));
}
static void upool_recycle(Chd *W, node_t *U, uint64_t cap) {
    if (W->upool_n == W->upool_cap) {
        W->upool_cap = W->upool_cap ? W->upool_cap * 2 : 64;
        W->upool = (node_t **)xrealloc(W->upool, W->upool_cap * sizeof(node_t *));
        W->ucap = (uint32_t *)xrealloc(W->ucap, W->upool_cap * sizeof(uint32_t));
    }
    W->upool[W->upool_n] = U;
    W->ucap[W->upool_n] = (uint32_t)cap;
    W->upool_n++;
}

static void dstr_grow_blist(DStr *D, uint32_t need) {
    if (D->cap < need) {
        D->cap = D->cap ? D->cap * 2 : 16;
        while (D->cap < need) D->cap *= 2;
        D->blist = (uint32_t *)xrealloc(D->blist, D->cap * sizeof(uint32_t));
    }
}
static void dstr_push_blk(DStr *D, uint32_t b) {
    dstr_grow_blist(D, D->nb + 1);
    D->blist[D->nb++] = b;
}

/* drop stale entries of block b; returns live count */
static uint32_t blk_compact(Chd *W, uint32_t b) {
    Block *B = &W->blk[b];
    uint32_t prev = NONE32, head = B->head, live = 0;
    while (head != NONE32) {
        Entry *e = &W->ent[head];
        if (e->stale) {
            if (prev == NONE32) B->head = e->next; else W->ent[prev].next = e->next;
        } else { prev = head; live++; }
        head = e->next;
    }
    B->cnt = live;
    return live;
}

/* first block index whose separator >= c; -1 if none (c above all seps) */
static int dstr_bsearch(Chd *W, DStr *D, Label c) {
    int lo = 0, hi = (int)D->nb - 1, ans = -1;
    while (lo <= hi) {
        int mid = (lo + hi) / 2;
        if (lbl_le(c, W->blk[D->blist[mid]].sep)) { ans = mid; hi = mid - 1; }
        else lo = mid + 1;
    }
    return ans;
}

/* Insert (Sec 3.4): keep-min, supersede elsewhere (rule EA). */
static void dstr_insert_impl(Chd *W, DStr *D, uint32_t v, Label c) {
    W->stat_inserts++;
    uint32_t e = W->live_ent[v];
    if (e != NONE32 && !W->ent[e].stale) {
        if (W->blk[W->ent[e].blk].owner == D && lbl_le(W->ent[e].val, c))
            return;                       /* live entry in D, value <= c */
        /* supersede: entry becomes stale wherever it lives */
        W->ent[e].stale = 1;
        Block *ob = &W->blk[W->ent[e].blk];
        ob->live--;
        if (ob->owner == D) D->live_total--;
    }
    /* owning block via separator binary search */
    int idx = dstr_bsearch(W, D, c);
    uint32_t b;
    if (idx < 0) { b = blk_new(W, c, NONE32, 0, 0, D); dstr_push_blk(D, b); }
    else b = D->blist[idx];
    uint32_t ne = ent_new(W, c, v, b);
    W->ent[ne].next = W->blk[b].head;
    W->blk[b].head = ne;
    W->blk[b].cnt++; W->blk[b].live++;
    D->live_total++;
    W->live_ent[v] = ne;
}
static void dstr_insert(Chd *W, DStr *D, uint32_t v, Label c) {
    PROF(6, dstr_insert_impl(W, D, v, c));
}

/* Delete (FIX-STALE / BM.29): O(1), global stale of the live entry. */
static void dstr_delete_impl(Chd *W, uint32_t v) {
    uint32_t e = W->live_ent[v];
    if (e == NONE32 || W->ent[e].stale) return;
    W->ent[e].stale = 1;
    Block *ob = &W->blk[W->ent[e].blk];
    ob->live--;
    if (ob->owner) ob->owner->live_total--;
    W->live_ent[v] = NONE32;
}
static void dstr_delete(Chd *W, uint32_t v) {
    PROF(14, dstr_delete_impl(W, v));
}

/* Merge (BM.14): splice the child's blocks into the parent's blist IN
 * SEPARATOR ORDER (the DS' invariant: blist sorted by block separator,
 * separators tight = block max).  With this and the insert rule (a key
 * enters the first block whose separator >= key), every key of an
 * ungathered block exceeds every gathered key, so the Pull property
 * S' = {y : val(y) < x} holds. */
static void dstr_merge_impl(Chd *W, DStr *D, DStr *C) {
    if (C->nb == 0) return;
    dstr_grow_blist(D, D->nb + C->nb + 8);
    uint64_t need = (uint64_t)D->nb + C->nb + 8;
    if (W->merge_nb_cap < need) {
        W->merge_nb_cap = W->merge_nb_cap ? W->merge_nb_cap : 64;
        while (W->merge_nb_cap < need) W->merge_nb_cap *= 2;
        W->merge_nb = (uint32_t *)xrealloc(W->merge_nb, W->merge_nb_cap * sizeof(uint32_t));
    }
    uint32_t *nb = W->merge_nb;
    uint32_t nn = 0, i = 0, j = 0;
    while (i < C->nb && j < D->nb) {
        uint32_t cb = C->blist[i], pb = D->blist[j];
        if (lbl_le(W->blk[cb].sep, W->blk[pb].sep)) {
            nb[nn++] = cb; W->blk[cb].owner = D; i++;
        } else {
            nb[nn++] = pb; j++;
        }
    }
    while (i < C->nb) { nb[nn++] = C->blist[i]; W->blk[C->blist[i]].owner = D; i++; }
    while (j < D->nb) nb[nn++] = D->blist[j++];
    memcpy(D->blist, nb, nn * sizeof(uint32_t));
    D->nb = nn;
    D->live_total += C->live_total;
    W->stat_merge_blks += C->nb;
}
static void dstr_merge(Chd *W, DStr *D, DStr *C) {
    PROF(7, dstr_merge_impl(W, D, C));
}

/* Worst-case O(n) partial selection on (val,eidx) pairs: after the call,
 * a[0..k) holds the k smallest elements (unordered). */
static void bfprt_select_se(SE *a, uint64_t n, uint64_t k) {
    while (n > 32) {
        /* gather medians of groups of 5 into a[0..m) */
        uint64_t m = 0;
        for (uint64_t i = 0; i + 5 <= n; i += 5) {
            for (int p = 1; p < 5; p++) {           /* insertion-sort 5 */
                SE t = a[i + p]; int q = p - 1;
                while (q >= 0 && lbl_lt(t.val, a[i + q].val)) { a[i + q + 1] = a[i + q]; q--; }
                a[i + q + 1] = t;
            }
            SE t = a[i + 2]; a[i + 2] = a[m]; a[m] = t;
            m++;
        }
        /* median of medians (recursive; destroys the group layout, which is
           fine because the partition below re-scans the whole array) */
        bfprt_select_se(a, m, m / 2);
        Label pivot = a[m / 2].val;
        /* three-way partition of [0,n) around pivot */
        uint64_t lt = 0, i = 0, gt = n;
        while (i < gt) {
            int c = lbl_cmp(a[i].val, pivot);
            if (c < 0)      { SE t = a[i]; a[i] = a[lt]; a[lt] = t; lt++; i++; }
            else if (c > 0) { gt--; SE t = a[i]; a[i] = a[gt]; a[gt] = t; }
            else i++;
        }
        if (k < lt) { n = lt; }
        else if (k < gt) { return; }              /* inside the equal run */
        else { k -= gt; a += gt; n -= gt; }
    }
    /* insertion sort for small n; first k are the smallest */
    for (uint64_t p = 1; p < n; p++) {
        SE t = a[p]; int64_t q = (int64_t)p - 1;
        while (q >= 0 && lbl_lt(t.val, a[q].val)) { a[q + 1] = a[q]; q--; }
        a[q + 1] = t;
    }
}
static void bfprt_select(Chd *W, uint64_t n, uint64_t k) {
    bfprt_select_se(W->sc, n, k);
}

/* For the small gathers typical inside the window (M = t, blocks ~M+1
 * entries), a plain insertion sort beats median-of-medians by a wide margin
 * and still partitions [0,M) | [M,n) exactly as required. */
static void se_insertion_sort(SE *a, uint64_t n) {
    for (uint64_t p = 1; p < n; p++) {
        SE t = a[p]; uint64_t q = p;
        while (q > 0 && lbl_lt(t.val, a[q - 1].val)) { a[q] = a[q - 1]; q--; }
        a[q] = t;
    }
}
static inline void select_first_m(Chd *W, uint64_t n, uint64_t M) {
    if (n <= 64) se_insertion_sort(W->sc, n);
    else bfprt_select(W, n, M);
}

/* ensure scratch holds at least need elements */
static void sc_ensure(Chd *W, uint64_t need) {
    if (W->sc_cap < need) {
        W->sc_cap = W->sc_cap ? W->sc_cap : (1u << 16);
        while (W->sc_cap < need) W->sc_cap *= 2;
        W->sc = xrealloc(W->sc, W->sc_cap * sizeof(*W->sc));
    }
}

/* Pull (BM.10):
 *   - compacts/splits front blocks until M+1 live entries are held;
 *   - returns the cnt = min(M, held) smallest keys (entries consumed);
 *   - *Bi = boundary label: smallest NON-selected live label, or the
 *     structure bound if everything was taken (short pull);
 *   - the unselected remainder becomes the new front block.
 * Selected keys are returned via W->sc[0..cnt) (val = current label). */
static uint64_t dstr_pull(Chd *W, DStr *D, Label *Bi) {
    W->stat_pulls++;
    uint64_t M = D->M;
    uint64_t held = 0;
    uint32_t gathered = 0;   /* how many front blocks were consumed */
    uint32_t *consumed = W->pull_consumed;
    uint64_t consumed_cap = W->pull_consumed_cap;
    if (consumed_cap < (uint64_t)D->nb + 8) {
        consumed_cap = (uint64_t)D->nb + 8;
        consumed = (uint32_t *)xrealloc(consumed, consumed_cap * sizeof(uint32_t));
        W->pull_consumed = consumed; W->pull_consumed_cap = consumed_cap;
    }
    for (;;) {
        /* drop empty front blocks */
        while (D->nb > 0 && W->blk[D->blist[0]].live == 0 &&
               W->blk[D->blist[0]].cnt == 0) {
            memmove(D->blist, D->blist + 1, (D->nb - 1) * sizeof(uint32_t));
            D->nb--;
        }
        if (D->nb == 0) { *Bi = D->bound; return 0; }
        uint32_t b0 = D->blist[0];
        if (W->blk[b0].cnt != W->blk[b0].live) {
            if (blk_compact(W, b0) == 0) { W->blk[b0].cnt = 0; continue; }
        }
        if (W->blk[b0].live > 2 * M && W->blk[b0].live > 8) {
            /* split front block at its value median */
            Block *B = &W->blk[b0];
            uint64_t n = 0;
            sc_ensure(W, B->cnt + 1);
            for (uint32_t e = B->head; e != NONE32; e = W->ent[e].next)
                if (!W->ent[e].stale) { W->sc[n].val = W->ent[e].val; W->sc[n].eidx = e; n++; }
            uint64_t half = n / 2;
            select_first_m(W, n, half);
            /* lower half: values <= median.  Rebuild two chains. */
            Label med = W->sc[half - 1].val;
            uint32_t lo_head = NONE32, hi_head = NONE32;
            for (uint64_t i = 0; i < n; i++) {
                uint32_t e = W->sc[i].eidx;
                if (i < half) { W->ent[e].next = lo_head; lo_head = e; }
                else        { W->ent[e].next = hi_head; hi_head = e; }
            }
            Label oldsep = B->sep;
            B->head = lo_head; B->cnt = (uint32_t)half; B->live = (uint32_t)half; B->sep = med;
            uint32_t b2 = blk_new(W, oldsep, hi_head, (uint32_t)(n - half), (uint32_t)(n - half), D);
            for (uint64_t i = half; i < n; i++)
                W->ent[W->sc[i].eidx].blk = b2;   /* keep entry->block mapping */
            /* insert b2 right after b0 */
            dstr_grow_blist(D, D->nb + 1);
            memmove(D->blist + 2, D->blist + 1, (D->nb - 1) * sizeof(uint32_t));
            D->blist[1] = b2; D->nb++;
            continue;
        }
        /* gather front block: remove it from blist, remember it */
        if (gathered == consumed_cap) {          /* splits may raise the count */
            consumed_cap *= 2;
            consumed = (uint32_t *)xrealloc(consumed, consumed_cap * sizeof(uint32_t));
            W->pull_consumed = consumed; W->pull_consumed_cap = consumed_cap;
        }
        consumed[gathered++] = b0;
        held += W->blk[b0].live;
        memmove(D->blist, D->blist + 1, (D->nb - 1) * sizeof(uint32_t));
        D->nb--;
        if (held >= M + 1 || D->nb == 0) break;
    }
    /* the gathered blocks (exactly `gathered`) hold `held` live entries */
    uint64_t nlive = held;
    sc_ensure(W, nlive + 1);
    uint64_t n = 0;
    for (uint32_t i = 0; i < gathered; i++) {
        uint32_t b = consumed[i];
        for (uint32_t e = W->blk[b].head; e != NONE32; e = W->ent[e].next) {
            if (W->ent[e].stale) continue;
            W->sc[n].val = W->ent[e].val; W->sc[n].eidx = e; n++;
            /* NOTE: not stale-ing here; selected entries are consumed below,
             * the remainder must stay LIVE and move to the new front block. */
        }
        W->blk[b].live = 0; W->blk[b].cnt = 0; W->blk[b].head = NONE32;
    }
    nlive = n;   /* trust the real chain walk, not the block live counters */
    if (nlive <= M) {           /* short pull: take everything */
        for (uint64_t i = 0; i < n; i++) {
            uint32_t e = W->sc[i].eidx;
            W->ent[e].stale = 1;
            W->live_ent[W->ent[e].key] = NONE32;
        }
        *Bi = D->bound;
        D->live_total -= nlive;
        return nlive;
    }
    /* select the M smallest */
    select_first_m(W, nlive, M);
    /* selected entries are consumed */
    for (uint64_t i = 0; i < M; i++) {
        uint32_t e = W->sc[i].eidx;
        W->ent[e].stale = 1;
        W->live_ent[W->ent[e].key] = NONE32;
    }
    D->live_total -= M;
    /* remainder stays live and moves to a fresh front block */
    uint32_t rhead = NONE32;
    Label rmax = W->sc[M].val;
    for (uint64_t i = M; i < nlive; i++) {
        uint32_t e = W->sc[i].eidx;
        W->ent[e].next = rhead; rhead = e;
        if (lbl_lt(rmax, W->sc[i].val)) rmax = W->sc[i].val;
    }
    uint32_t b = blk_new(W, rmax, rhead, (uint32_t)(nlive - M), (uint32_t)(nlive - M), D);
    for (uint64_t i = M; i < nlive; i++)
        W->ent[W->sc[i].eidx].blk = b;
    dstr_grow_blist(D, D->nb + 1);
    memmove(D->blist + 1, D->blist, D->nb * sizeof(uint32_t));
    D->blist[0] = b; D->nb++;
    *Bi = W->sc[M].val;
    return M;
}

/* IsEmpty with lazy front compaction */
static int dstr_isempty(Chd *W, DStr *D) {
    while (D->nb > 0) {
        uint32_t b = D->blist[0];
        if (W->blk[b].live > 0) return 0;
        if (W->blk[b].cnt == 0) {
            memmove(D->blist, D->blist + 1, (D->nb - 1) * sizeof(uint32_t));
            D->nb--;
            continue;
        }
        if (blk_compact(W, b) > 0) return 0;
        W->blk[b].cnt = 0;
    }
    return 1;
}

/* ------------------------------------------------------------------ */
/* Base-case indexed binary heap on labels (IHeap, Sec 5 T0)           */
/* ------------------------------------------------------------------ */

typedef struct {
    Label  *key;   /* 1-indexed heap entries (labels at push/decrease time) */
    node_t *id;    /* vertex ids, 1-indexed */
    uint32_t *pos; /* vertex -> slot+1 (0 = absent); EXTERNAL array */
    uint32_t sz, cap;
} IHeap;

/* The heap arrays are borrowed from the workspace (W->ih_key/W->ih_id):
 * base-case calls run strictly one-at-a-time (depth-first recursion), so a
 * single shared backing store kills the per-call malloc/free churn. */
static void ih_init(Chd *W, IHeap *h, uint32_t cap, uint32_t *pos) {
    uint64_t need = cap ? cap : 16;
    if (W->ih_cap < need) {
        W->ih_cap = W->ih_cap ? W->ih_cap : 256;
        while (W->ih_cap < need) W->ih_cap *= 2;
        W->ih_key = (Label *)xrealloc(W->ih_key, (W->ih_cap + 1) * sizeof(Label));
        W->ih_id  = (node_t *)xrealloc(W->ih_id, (W->ih_cap + 1) * sizeof(node_t));
    }
    h->key = W->ih_key; h->id = W->ih_id; h->pos = pos;
    h->sz = 0; h->cap = (uint32_t)W->ih_cap;
}

static inline int ih_lt(Label a, Label b) { return lbl_lt(a, b); }

/* 4-ary indexed heap: shallower than binary (log_4 n levels), same number of
 * comparisons per node visit, fewer cache lines touched on the sift paths.
 * 1-indexed; parent(i) = (i+2)/4, children(i) = 4i-2 .. 4i+1. */
static void ih_push(Chd *W, IHeap *h, node_t v, Label k) {
    if (h->sz == h->cap) {
        W->ih_cap *= 2;
        W->ih_key = (Label *)xrealloc(W->ih_key, (W->ih_cap + 1) * sizeof(Label));
        W->ih_id  = (node_t *)xrealloc(W->ih_id, (W->ih_cap + 1) * sizeof(node_t));
        h->key = W->ih_key; h->id = W->ih_id; h->cap = (uint32_t)W->ih_cap;
    }
    uint32_t i = ++h->sz;
    while (i > 1) {
        uint32_t p = (i + 2) / 4;
        if (!ih_lt(k, h->key[p])) break;
        h->key[i] = h->key[p]; h->id[i] = h->id[p]; h->pos[h->id[i]] = i;
        i = p;
    }
    h->key[i] = k; h->id[i] = v; h->pos[v] = i;
}
static void ih_decrease(Chd *W, IHeap *h, node_t v, Label k) {
    uint32_t i = h->pos[v];
    if (i == 0) { ih_push(W, h, v, k); return; }
    if (!ih_lt(k, h->key[i])) return;
    while (i > 1) {
        uint32_t p = (i + 2) / 4;
        if (!ih_lt(k, h->key[p])) break;
        h->key[i] = h->key[p]; h->id[i] = h->id[p]; h->pos[h->id[i]] = i;
        i = p;
    }
    h->key[i] = k; h->id[i] = v; h->pos[v] = i;
}
static node_t ih_pop(IHeap *h, Label *out) {
    node_t r = h->id[1]; *out = h->key[1];
    h->pos[r] = 0;
    if (h->sz == 1) { h->sz = 0; return r; }
    Label k = h->key[h->sz]; node_t v = h->id[h->sz]; h->sz--;
    uint32_t i = 1;
    for (;;) {
        uint32_t c = i * 4 - 2;          /* first child */
        if (c > h->sz) break;
        uint32_t mc = c;                 /* smallest child */
        if (c + 1 <= h->sz && ih_lt(h->key[c + 1], h->key[mc])) mc = c + 1;
        if (c + 2 <= h->sz && ih_lt(h->key[c + 2], h->key[mc])) mc = c + 2;
        if (c + 3 <= h->sz && ih_lt(h->key[c + 3], h->key[mc])) mc = c + 3;
        if (!ih_lt(h->key[mc], k)) break;
        h->key[i] = h->key[mc]; h->id[i] = h->id[mc]; h->pos[h->id[i]] = i;
        i = mc;
    }
    h->key[i] = k; h->id[i] = v; h->pos[v] = i;
    return r;
}

/* ------------------------------------------------------------------ */
/* FindPivots-HD (FH.1-FH.26)                                          */
/* ------------------------------------------------------------------ */

/* Per-invocation buffers (reset each FindPivots call). */
typedef struct { node_t v; uint32_t next; } TVNode;

typedef struct FPB {
    TVNode  *tv;     /* tree vertex nodes (linked; per-tree chains) */
    uint32_t tv_n, tv_cap;
    uint32_t *thead, *tcnt; uint32_t t_n, t_cap;   /* tree list */
    node_t *H;       /* search heap (unsorted array) */
    uint32_t h_cap;
    node_t *K;       /* touched list (search tree vertex list) */
    int32_t *kpar;   /* first-discovery parent per K position */
    uint32_t *kedge; /* edge slot per K position */
    node_t *Ux;      /* virtual settlements of all runs this invocation */
    uint32_t Ux_n, Ux_cap;
    node_t *Q;  uint32_t Q_n, Q_cap;
} FPB;

static void fpb_reset(FPB *f, uint32_t k, uint32_t Ssz) {
    uint32_t kmax = 4 * k + 16;
    uint32_t need = (uint64_t)kmax * Ssz + 64;
    if (f->tv_cap < need) {
        f->tv_cap = need * 2;
        f->tv = (TVNode *)xrealloc(f->tv, f->tv_cap * sizeof(TVNode));
    }
    f->tv_n = 0;
    if (f->t_cap < Ssz + 2) {
        f->t_cap = Ssz + 2;
        f->thead  = (uint32_t *)xrealloc(f->thead, f->t_cap * sizeof(uint32_t));
        f->tcnt   = (uint32_t *)xrealloc(f->tcnt,  f->t_cap * sizeof(uint32_t));
    }
    f->t_n = 0;
    if (f->h_cap < kmax + 2) {
        f->h_cap = kmax + 2;
        f->H = (node_t *)xrealloc(f->H, f->h_cap * sizeof(node_t));
        f->K = (node_t *)xrealloc(f->K, f->h_cap * sizeof(node_t));
        f->kpar = (int32_t *)xrealloc(f->kpar, f->h_cap * sizeof(int32_t));
        f->kedge = (uint32_t *)xrealloc(f->kedge, f->h_cap * sizeof(uint32_t));
    }
    if (f->Ux_cap < Ssz + 2) { f->Ux_cap = 2 * (Ssz + 2); f->Ux = (node_t *)xrealloc(f->Ux, f->Ux_cap * sizeof(node_t)); }
    f->Ux_n = 0;
    if (f->Q_cap < Ssz + 2) { f->Q_cap = Ssz + 2; f->Q = (node_t *)xrealloc(f->Q, f->Q_cap * sizeof(node_t)); }
    f->Q_n = 0;
}

/* extract-min of the unsorted search heap H[0..hn): scans current labels */
static node_t fh_extract_min(Chd *W, node_t *H, uint32_t *hn) {
    uint32_t bi = 0;
    Label bv = W->d[H[0]];
    for (uint32_t i = 1; i < *hn; i++)
        if (lbl_lt(W->d[H[i]], bv)) { bv = W->d[H[i]]; bi = i; }
    node_t u = H[bi];
    H[bi] = H[--(*hn)];
    return u;
}
static int fh_contains(node_t *H, uint32_t hn, node_t v) {
    for (uint32_t i = 0; i < hn; i++) if (H[i] == v) return 1;
    return 0;
}

/* One bounded local search (FB.3-FB.19 / FD.5-FD.19 body) rooted at x.
 *
 * This is the flat-C rendering of the paper's InnerSearch(x): a capped
 * (tau = k) Dijkstra ball from x on the global labels, with walls on the
 * vertices of the trees built so far.  Extracted vertices are settled
 * VIRTUALY (ustamp = inv_id): in-run extraction order makes their labels
 * final, and the settlement mark doubles as the wall for later runs and
 * the safety guard for Relax.  Virtual marks are cleared by find_pivots
 * once the invocation's trees/pivots/W have been produced; failed runs
 * hand their settled ball to W (BM.26 makes it permanent at call end).
 *
 * Every touched vertex ends up either virtually settled (shared Ux list,
 * which feeds W) or in a tree — no vertex is left "hidden" with a label
 * outside every structure.  Scans do NOT advance W->ptr: a vertex settled
 * for real later re-scans its full range (the virtual scan is exploratory
 * only, and W->ptr commits only on real settlements). */
static void fh_search(Chd *W, FPB *f, node_t x, Label B, Label LX,
                      uint32_t inv_id, uint32_t k) {
    W->stat_fp_searches++;
    uint32_t sid = ++W->ctr;
    const uint32_t KMAX = 4 * k + 16;
    uint32_t hn = 0;
    uint32_t kn = 0;
    uint32_t ux0 = f->Ux_n;
    f->H[hn++] = x;
    f->K[kn++] = x;
    W->kst[x] = sid;
    f->kpar[0] = -1;
    f->kedge[0] = EID_NONE;
    int hit = 0;
    node_t hu = 0;
    uint32_t hs = EID_NONE;
    uint32_t htree = NONE32;

    while (hn > 0 && f->Ux_n - ux0 < k && kn < KMAX) {
        node_t u = fh_extract_min(W, f->H, &hn);
        if (W->ustamp[u]) continue;                     /* already settled */
        /* virtual settlement (in-run Dijkstra order => label final) */
        W->ustamp[u] = inv_id;
        if (f->Ux_n == f->Ux_cap) {
            f->Ux_cap = f->Ux_cap ? f->Ux_cap * 2 : 64;
            f->Ux = (node_t *)xrealloc(f->Ux, f->Ux_cap * sizeof(node_t));
        }
        f->Ux[f->Ux_n++] = u;
        Label du = W->d[u];
        node_t s = W->g.gSt[u], e = W->g.gSt[u + 1];
        for (; s < e; s++) {
            if (W->g.gdel[s]) continue;
            weight_t w = W->g.gW[s];
            /* cand = d[u] (+) e; range stop: slots sorted by weight, d[u]
               fixed during the scan (prefix fact P).  len-only pre-break is
               exact (cand.len = du.len + w): ties fall through to the full
               label order below. */
            double clen = du.len + w;
            if (clen > B.len) break;
            Label cand; cand.len = clen; cand.hops = du.hops + 1; cand.eid = s;
            if (!lbl_lt(cand, B)) break;
            node_t v = W->g.gHead[s];
            if (lbl_lt(W->d[v], LX)) {                  /* Lemma L */
                W->g.gdel[s] = 1;
                W->g.ghas_del = 1;
                W->stat_deleted++;
                continue;
            }
            if (W->ustamp[v]) continue;                 /* settled: dead end */
            if (W->fmark[v] == inv_id) {                /* walled: first hit */
                if (!hit) { hit = 1; hu = u; hs = s; htree = W->treeof[v]; }
                continue;
            }
            int ok = RELAX(W, v, u, cand);
            if (!ok) continue;
            if (W->kst[v] != sid) {                     /* newly touched */
                W->kst[v] = sid;
                f->K[kn] = v;
                f->kpar[kn] = (int32_t)u;
                f->kedge[kn] = s;
                kn++;
                f->H[hn++] = v;
                if (kn >= KMAX) break;
            } else if (!fh_contains(f->H, hn, v)) {
                f->H[hn++] = v;
            }
        }
    }
    if (hit) {                                          /* FB.11: merge */
        for (uint32_t i = 1; i < kn; i++) {
            node_t y = f->K[i];
            TVNode nd; nd.v = y; nd.next = f->thead[htree];
            f->tv[f->tv_n] = nd; f->thead[htree] = f->tv_n++;
            W->treeof[y] = htree;
            W->tparent[y] = f->kpar[i];
            W->tedge[y] = f->kedge[i];
        }
        /* cross edge (hu, hs): edge of H with tail in K, head in htree;
           it is what connects this run's component to the existing tree */
        W->tparent[x] = (int32_t)hu;
        W->tedge[x] = hs;
        {
            TVNode nd; nd.v = x; nd.next = f->thead[htree];
            f->tv[f->tv_n] = nd; f->thead[htree] = f->tv_n++;
            W->treeof[x] = htree;
        }
        f->tcnt[htree] += kn;
        for (uint32_t i = 0; i < kn; i++) W->fmark[f->K[i]] = inv_id;
    } else if (kn < KMAX && f->Ux_n - ux0 < k && hn == 0) {
        /* FB.18/FD.19 failed: ball exhausted, < k settlements, no hit */
        f->Q[f->Q_n++] = x;
        /* W gets Ux (all runs share f->Ux; find_pivots dedups it into W) */
    } else {                                            /* FB.15: new tree */
        uint32_t tv = f->t_n++;
        f->thead[tv] = NONE32;
        f->tcnt[tv] = kn;
        for (uint32_t i = 0; i < kn; i++) {
            node_t y = f->K[i];
            TVNode nd; nd.v = y; nd.next = f->thead[tv];
            f->tv[f->tv_n] = nd; f->thead[tv] = f->tv_n++;
            W->treeof[y] = tv;
            W->tparent[y] = f->kpar[i];
            W->tedge[y] = f->kedge[i];
            W->fmark[y] = inv_id;
        }
    }
}

/* ------------------------------------------------------------------ */
/* Tree partition (PT.1-PT.9, DMSY26 Alg 5)                            */
/* ------------------------------------------------------------------ */

typedef struct {
    uint32_t v; uint32_t next;
} PNode;

/* Partition tree tv (vertices f->verts[tstart..tstart+cnt)) into groups of
 * sizes in [s, 3s).  Groups are emitted as linked lists over a per-tree node
 * arena; emits group (head,count) pairs into gh/gc. */
static void partition_tree(Chd *W, FPB *f, uint32_t tv, uint32_t s,
                           PNode *node, uint32_t *nxt_free,
                           uint32_t *gh, uint32_t *gc, uint32_t *gn) {
    uint32_t tc = f->tcnt[tv];
    if (tc == 0) return;
    /* local index mapping via kst stamp reuse (search ids are dead here) */
    uint32_t lid = ++W->ctr;
    /* per-local-vertex arrays sized tc */
    uint32_t *lidx = (uint32_t *)malloc((tc + 1) * sizeof(uint32_t));
    int32_t  *par  = (int32_t *)malloc((tc + 1) * sizeof(int32_t));
    uint32_t *ch_head = (uint32_t *)malloc((tc + 1) * sizeof(uint32_t));
    uint32_t *ch_next = (uint32_t *)malloc((tc + 1) * sizeof(uint32_t));
    {
        uint32_t i = 0;
        for (uint32_t e = f->thead[tv]; e != NONE32 && i < tc; e = f->tv[e].next) {
            node_t v = f->tv[e].v;
            lidx[i] = v;
            W->kst[v] = lid;
            W->treeof[v] = i;              /* local id scratch (invocation over) */
            ch_head[i] = NONE32;
            i++;
        }
        tc = i;
    }
    uint32_t root = 0;
    for (uint32_t i = 0; i < tc; i++) {
        node_t v = lidx[i];
        int32_t p = W->tparent[v];
        if (p < 0) { par[i] = -1; root = i; }
        else {
            uint32_t pl = W->treeof[p];    /* local id of parent */
            par[i] = (int32_t)pl;
            ch_next[i] = ch_head[pl];
            ch_head[pl] = i;
        }
    }
    /* iterative post-order DFS accumulating subtree sets (PT.3-PT.6).
       Each frame accumulates Uv (linked list) starting as {v}; when a child
       returns, its set is spliced into the parent's and the parent cuts a
       group as soon as |Uv| >= s (PT.5), resetting Uv = {v}. */
    uint32_t *st_v   = (uint32_t *)malloc((tc + 1) * sizeof(uint32_t));
    uint32_t *st_ci  = (uint32_t *)malloc((tc + 1) * sizeof(uint32_t));
    uint32_t *uv_h   = (uint32_t *)malloc((tc + 1) * sizeof(uint32_t));
    uint32_t *uv_t   = (uint32_t *)malloc((tc + 1) * sizeof(uint32_t));
    uint32_t *uv_c   = (uint32_t *)malloc((tc + 1) * sizeof(uint32_t));
    uint32_t sp = 0;
    uint32_t root_self = (*nxt_free)++;
    node[root_self].v = lidx[root]; node[root_self].next = NONE32;
    st_v[0] = root; st_ci[0] = ch_head[root];
    uv_h[0] = uv_t[0] = root_self; uv_c[0] = 1;
    uint32_t rest_h = NONE32, rest_c = 0;
    for (;;) {
        uint32_t v = st_v[sp];
        uint32_t ci = st_ci[sp];
        if (ci != NONE32) {
            st_ci[sp] = ch_next[ci];
            sp++;
            uint32_t self = (*nxt_free)++;
            node[self].v = lidx[ci]; node[self].next = NONE32;
            st_v[sp] = ci; st_ci[sp] = ch_head[ci];
            uv_h[sp] = uv_t[sp] = self; uv_c[sp] = 1;
            continue;
        }
        /* frame v finished: return its set to the parent (root -> rest) */
        uint32_t h = uv_h[sp], t = uv_t[sp], c = uv_c[sp];
        if (sp == 0) { rest_h = h; rest_c = c; break; }
        sp--;
        uint32_t p = st_v[sp];
        if (h != NONE32) {
            /* prepend child list (h..t) to the parent's set */
            if (uv_h[sp] == NONE32) { uv_h[sp] = h; uv_t[sp] = t; }
            else { node[t].next = uv_h[sp]; uv_h[sp] = h; }
        }
        uv_c[sp] += c;
        while (uv_c[sp] >= s) {
            gh[*gn] = uv_h[sp]; gc[*gn] = uv_c[sp]; (*gn)++;
            uint32_t self = (*nxt_free)++;
            node[self].v = lidx[p]; node[self].next = NONE32;
            uv_h[sp] = uv_t[sp] = self; uv_c[sp] = 1;
        }
    }
    /* PT.7-PT.8: rest handling */
    if (*gn == 0) {
        if (rest_c > 0) { gh[0] = rest_h; gc[0] = rest_c; *gn = 1; }
    } else if (rest_c > 0) {
        uint32_t last = *gn - 1;
        uint32_t t = rest_h;
        while (node[t].next != NONE32) t = node[t].next;
        node[t].next = gh[last];
        gh[last] = rest_h;
        gc[last] += rest_c;
    }
    free(lidx); free(par); free(ch_head); free(ch_next);
    free(st_v); free(st_ci); free(uv_h); free(uv_t); free(uv_c);
    (void)lid;
}

/* ------------------------------------------------------------------ */
/* MakePivots (MP.1-MP.10)                                             */
/* ------------------------------------------------------------------ */

typedef struct {
    node_t  *mem;    /* Pl group member vertices */
    uint32_t mem_n, mem_cap;
    uint32_t *gstart, *gcnt; uint32_t g_n, g_cap;
    node_t  *Q;  uint32_t Q_n;
    node_t  *W;  uint32_t W_n;
} Pivots;

static void pivots_free(Pivots *P) {
    free(P->mem); free(P->gstart); free(P->gcnt); free(P->Q); free(P->W);
    memset(P, 0, sizeof(*P));
}

/* FindPivots-HD + MakePivots: produces pivot groups, Q and W for a call. */
static void find_pivots(Chd *W, Label B, node_t *S, uint32_t Ssz, uint32_t k, Pivots *P) {
    if (!W->fpb) W->fpb = (struct FPB *)calloc(1, sizeof(struct FPB));
    FPB *f = W->fpb;
    fpb_reset(f, k, Ssz);
    W->stat_fp_invoc++;

    /* FH.1: L_X = min({B} cup {d[x] : x in S}) */
    Label LX = B;
    for (uint32_t i = 0; i < Ssz; i++)
        if (lbl_lt(W->d[S[i]], LX)) LX = W->d[S[i]];

    uint32_t inv_id = ++W->ctr;
    for (uint32_t i = 0; i < Ssz; i++) {
        node_t x = S[i];
        if (W->fmark[x] == inv_id) continue;                    /* FB.4 */
        if (W->ustamp[x]) continue;                             /* settled */
        PROF(3, fh_search(W, f, x, B, LX, inv_id, k));
    }

    /* MakePivots */
    memset(P, 0, sizeof(*P));
    P->Q = (node_t *)malloc((f->Q_n + 1) * sizeof(node_t));
    memcpy(P->Q, f->Q, f->Q_n * sizeof(node_t)); P->Q_n = f->Q_n;
    P->W = (node_t *)malloc((f->Ux_n + 1) * sizeof(node_t));
    /* W = dedup of all runs' virtually-settled balls (MP.9).  Includes
     * new-tree runs' settlements (labels final by in-run extraction order);
     * BM.26 settles them permanently at call end. */
    uint32_t wid = ++W->ctr;
    uint32_t wn = 0;
    for (uint32_t i = 0; i < f->Ux_n; i++) {
        node_t v = f->Ux[i];
        if (W->wstamp[v] == wid) continue;
        W->wstamp[v] = wid;
        P->W[wn++] = v;
    }
    P->W_n = wn;
    /* virtual settlements end with the invocation: clear the marks so the
     * real structures (D, pivots, W) drive the rest of the call */
    for (uint32_t i = 0; i < f->Ux_n; i++) W->ustamp[f->Ux[i]] = 0;

    /* MP.2 stamps */
    uint32_t sid = ++W->ctr;
    for (uint32_t i = 0; i < Ssz; i++) W->inSst[S[i]] = sid;
    for (uint32_t i = 0; i < P->Q_n; i++) W->inQst[P->Q[i]] = sid;
    uint32_t aid = ++W->ctr;

    /* partition each tree, filter cur (MP.4-MP.8) */
    PNode *node = (PNode *)malloc((f->tv_n + f->tv_n / 2 + 64) * sizeof(PNode));
    uint32_t nxt_free = 0;
    uint32_t *gh = (uint32_t *)malloc((f->tv_n + 2) * sizeof(uint32_t));
    uint32_t *gc = (uint32_t *)malloc((f->tv_n + 2) * sizeof(uint32_t));
    for (uint32_t tv = 0; tv < f->t_n; tv++) {
        uint32_t gn = 0;
        nxt_free = 0;
        partition_tree(W, f, tv, k, node, &nxt_free, gh, gc, &gn);
        for (uint32_t gi = 0; gi < gn; gi++) {
            /* cur = S-members of the group, not in Q, unassigned */
            uint32_t start = P->mem_n, cnt = 0;
            for (uint32_t e = gh[gi]; e != NONE32; e = node[e].next) {
                node_t v = node[e].v;
                if (W->inSst[v] != sid) continue;
                if (W->inQst[v] == sid) continue;
                if (W->asgst[v] == aid) continue;
                W->asgst[v] = aid;
                if (P->mem_n == P->mem_cap) {
                    P->mem_cap = P->mem_cap ? P->mem_cap * 2 : 64;
                    P->mem = (node_t *)xrealloc(P->mem, P->mem_cap * sizeof(node_t));
                }
                P->mem[P->mem_n++] = v;
                cnt++;
            }
            if (cnt == 0) { P->mem_n = start; continue; }   /* MP.8 */
            if (P->g_n == P->g_cap) {
                P->g_cap = P->g_cap ? P->g_cap * 2 : 16;
                P->gstart = (uint32_t *)xrealloc(P->gstart, P->g_cap * sizeof(uint32_t));
                P->gcnt   = (uint32_t *)xrealloc(P->gcnt,   P->g_cap * sizeof(uint32_t));
            }
            P->gstart[P->g_n] = start;
            P->gcnt[P->g_n] = cnt;
            P->g_n++;
        }
    }
    free(node); free(gh); free(gc);
}

/* ------------------------------------------------------------------ */
/* Call state (BM.1-BM.31)                                             */
/* ------------------------------------------------------------------ */

typedef struct { uint32_t j, prev, owner, midx; } PMNode; /* pmem stack node */

typedef struct {
    uint32_t id;         /* call id (ustamp / pmem owner) */
    uint32_t level;
    Label    B;
    DStr     D;
    /* Pl groups */
    node_t  *plmem;  uint32_t plmem_n, plmem_cap;
    uint32_t *gstart, *gcnt; uint32_t g_n, g_cap;
    node_t  *piv;    uint32_t piv_cap;
    uint8_t *gdead;  uint32_t gdead_cap;   /* per pl member */
    /* pmem stack nodes (bump) */
    PMNode  *pm;     uint32_t pm_n, pm_cap;
    /* J set */
    uint32_t *J;     uint32_t Jn, Jcap;
    /* U accumulation */
    node_t  *U;      uint64_t Un, Ucap;
    /* iteration buffers */
    node_t  *Si;     uint64_t Sicap;
    node_t  *Wp;     uint64_t Wpcap;
    node_t  *W;      uint32_t Wn;     /* FindPivots W (retained for BM.26) */
    IHeap    heap;
} Call;

typedef struct { Label Bp; node_t *U; uint64_t Un, Ucap; DStr *D; } Ret;

static void call_init(Chd *W, Call *c, uint32_t level, Label B) {
    memset(c, 0, sizeof(*c));
    c->id = ++W->ctr;
    c->level = level;
    c->B = B;
    dstr_init(&c->D, W->Mtab[level], B);
    memset(&c->heap, 0, sizeof(c->heap));
}
static void call_free(Chd *W, Call *c) {
    dstr_recycle(W, &c->D);
    free(c->plmem); free(c->gstart); free(c->gcnt); free(c->piv);
    free(c->gdead); free(c->pm); free(c->J);
    if (c->U) upool_recycle(W, c->U, c->Ucap);
    free(c->Si); free(c->Wp);
}

static void pm_push(Chd *W, Call *c, node_t v, uint32_t j, uint32_t midx) {
    if (c->pm_n == c->pm_cap) {
        c->pm_cap = c->pm_cap ? c->pm_cap * 2 : 64;
        c->pm = (PMNode *)xrealloc(c->pm, c->pm_cap * sizeof(PMNode));
    }
    PMNode *n = &c->pm[c->pm_n];
    n->j = j; n->owner = c->id;
    n->midx = midx;
    n->prev = W->pm_top[v];
    W->pm_top[v] = c->pm_n + 1;
    c->pm_n++;
}
static void pm_pop(Chd *W, Call *c, node_t v) {
    uint32_t t = W->pm_top[v];
    if (t == 0) return;
    PMNode *n = &c->pm[t - 1];
    if (n->owner != c->id) return;      /* not ours: leave (shouldn't happen) */
    W->pm_top[v] = n->prev;
}
/* Pmem(x, owner=this call): group index or NONE32 */
static uint32_t pm_group(Chd *W, Call *c, node_t v) {
    uint32_t t = W->pm_top[v];
    if (t == 0) return NONE32;
    PMNode *n = &c->pm[t - 1];
    return (n->owner == c->id) ? n->j : NONE32;
}

static void call_U_append(Chd *W, Call *c, node_t v) {
    if (c->Un == c->Ucap) {
        if (c->U == NULL) {
            c->U = upool_alloc(W, &c->Ucap);   /* recycled buffer if available */
        } else {
            c->Ucap = c->Ucap ? c->Ucap * 2 : 256;
            c->U = (node_t *)xrealloc(c->U, c->Ucap * sizeof(node_t));
        }
    }
    c->U[c->Un++] = v;
    W->ustamp[v] = c->id;
}

/* forward decl */
static void bmssp(Chd *W, Label B, node_t *S, uint64_t Ssz, uint32_t level,
                  uint64_t tau, Ret *ret);

/* ------------------------------------------------------------------ */
/* Base case BC.1-BC.9: bounded Dijkstra on indexed binary heap        */
/* ------------------------------------------------------------------ */
static void base_case(Chd *W, Call *c, Label B, node_t *S, uint64_t Ssz,
                      uint64_t tau, Ret *ret) {
    W->stat_base_calls++;
    Red *G = &W->g;
    DStr *D0 = dstr_alloc(W, 1, B);
    ih_init(W, &c->heap, 256, W->hpos);

    for (uint64_t i = 0; i < Ssz; i++) {
        node_t x = S[i];
        if (W->ustamp[x]) continue;         /* settled: permanently deleted */
        ih_push(W, &c->heap, x, W->d[x]);   /* BC.2 (structure = heap) */
    }

    while (c->heap.sz > 0) {
        if (c->Un >= tau) break;                        /* BC.5 */
        Label val;
        node_t u = ih_pop(&c->heap, &val);
        call_U_append(W, c, u);
        /* BC.7: settle scan of the static range prefix below B.
         * D0 is intentionally NOT maintained during the loop: an unsettled
         * S-member or relaxed vertex is always still keyed in the heap, so
         * at BC.8 the heap contents alone reproduce D0 exactly (settled keys
         * were popped; never-settled keys remain). */
        Label du = W->d[u];
        node_t s = G->gSt[u], e = G->gSt[u + 1];
        node_t stop = s;
        const int has_del = G->ghas_del;
        PROF(8, for (; s < e; s++) {
            if (has_del && G->gdel[s]) continue;        /* Lemma L deleted */
            /* len-only pre-break is exact; ties fall through to the full
               label compare.  cand is built only for unsettled heads: labels
               are non-decreasing in s, so a skipped slot cannot postpone the
               window break past the slot that triggers it. */
            double clen = du.len + G->gW[s];
            if (clen > B.len) break;
            node_t v = G->gHead[s];
            if (W->ustamp[v]) continue;
            Label cand; cand.len = clen; cand.hops = du.hops + 1; cand.eid = s;
            if (!lbl_lt(cand, B)) break;                /* window */
            int ok = RELAX(W, v, u, cand);
            /* settle scans may re-encounter already-settled vertices by
             * equality: ok stays 1, but they must never re-enter the heap. */
            /* ok==1 implies ustamp[v]==0 (chd_relax refuses settled heads).
             * On ok, d[v] == cand: a strict decrease wrote cand, and equality
             * means cand WAS d[v], so the heap can take cand without reloading
             * W->d[v]. */
            if (ok) ih_decrease(W, &c->heap, v, cand);
            stop = s + 1;
        });
        W->ptr[u] = stop;
    }
    /* BC.8 */
    Label Bp = (c->heap.sz == 0) ? B : c->heap.key[1];
    /* conversion: leftover heap keys -> fresh level-0 DS' (v1.5 D1) */
    for (uint32_t i = 1; i <= c->heap.sz; i++) {
        node_t v = c->heap.id[i];
        dstr_insert(W, D0, v, W->d[v]);
        W->hpos[v] = 0;
    }
    ret->Bp = Bp;
    ret->U = c->U; ret->Un = c->Un; ret->Ucap = c->Ucap; ret->D = D0;
}

/* ------------------------------------------------------------------ */
/* BMSSP core (BM.1-BM.31)                                             */
/* ------------------------------------------------------------------ */
static uint64_t g_si_stamp = 0;   /* Si dedup stamp (per-run; values reset per use) */

static void bmssp(Chd *W, Label B, node_t *S, uint64_t Ssz, uint32_t level,
                  uint64_t tau, Ret *ret) {
    W->stat_calls++;
    Call c;
    call_init(W, &c, level, B);
    Red *G = &W->g;

    if (level == 0) {
        PROF(4, base_case(W, &c, B, S, Ssz, tau, ret));
        /* base_case consumed Call c; free only aux (U transferred) */
        c.U = NULL;
        call_free(W, &c);
        return;
    }

    /* BM.3 */
    DStr *D = &c.D;

    /* BM.4: FindPivots-HD */
    Pivots P;
    PROF(2, find_pivots(W, B, S, (uint32_t)Ssz, W->k, &P));
    c.W = P.W; c.Wn = P.W_n;   /* retained for BM.26; P.W freed with call */

    /* BM.5-BM.7: register groups, elect pivots, insert */
    c.g_n = P.g_n;
    if (c.g_n) {
        c.gstart = (uint32_t *)xrealloc(c.gstart, c.g_n * sizeof(uint32_t));
        c.gcnt   = (uint32_t *)xrealloc(c.gcnt,   c.g_n * sizeof(uint32_t));
        c.piv    = (node_t *)xrealloc(c.piv, c.g_n * sizeof(node_t));
        c.plmem_n = P.mem_n;
        c.plmem = (node_t *)xrealloc(c.plmem, (P.mem_n + 1) * sizeof(node_t));
        memcpy(c.plmem, P.mem, P.mem_n * sizeof(node_t));
        c.gdead = (uint8_t *)xrealloc(c.gdead, (P.mem_n + 1));
        memset(c.gdead, 0, P.mem_n + 1);
        for (uint32_t j = 0; j < c.g_n; j++) {
            c.gstart[j] = P.gstart[j];
            c.gcnt[j] = P.gcnt[j];
            /* BM.6: PushPmem */
            node_t best = c.plmem[P.gstart[j]];
            Label bd = W->d[best];
            for (uint32_t i = 0; i < P.gcnt[j]; i++) {
                uint32_t midx = P.gstart[j] + i;
                node_t x = c.plmem[midx];
                pm_push(W, &c, x, j, midx);
                if (lbl_lt(W->d[x], bd)) { bd = W->d[x]; best = x; }
            }
            c.piv[j] = best;                          /* BM.7 */
            dstr_insert(W, D, best, W->d[best]);
        }
    }
    free(P.mem); free(P.gstart); free(P.gcnt); free(P.Q);  /* P.W -> c.W */

    Label Bp = B;   /* BM.8: B' := min(B, min_j d[piv[j]]) */
    if (c.g_n) {
        for (uint32_t j = 0; j < c.g_n; j++)
            if (lbl_lt(W->d[c.piv[j]], Bp)) Bp = W->d[c.piv[j]];
    }

    /* BM.9 main loop */
    while (c.Un <= tau) {
        if (dstr_isempty(W, D)) break;
        Label Bi;
        uint64_t cnt;
        PROF(5, cnt = dstr_pull(W, D, &Bi));
        if (cnt == 0) break;
        /* BM.11: Si = pulled keys */
        if (c.Sicap < cnt + 64) {
            c.Sicap = (cnt + 64) * 2;
            c.Si = (node_t *)xrealloc(c.Si, c.Sicap * sizeof(node_t));
        }
        uint64_t sn = 0;
        uint32_t si_st = (uint32_t)(++g_si_stamp);  /* dedicated dedup array */
        if (si_st == 0) si_st = (uint32_t)(++g_si_stamp);
        uint64_t pn = 0;                         /* pulled keys actually kept */
        for (uint64_t i = 0; i < cnt; i++) {
            node_t v = W->ent[W->sc[i].eidx].key;
            if (W->siddup[v] == si_st) continue;
            W->siddup[v] = si_st;
            c.Si[pn++] = v;
        }
        sn = pn;
        /* BM.12: expansion */
        for (uint64_t i = 0; i < pn; i++) {
            node_t x = c.Si[i];
            uint32_t j = pm_group(W, &c, x);
            if (j == NONE32 || c.piv[j] != x) continue;
            for (uint32_t t = 0; t < c.gcnt[j]; t++) {
                uint32_t midx = c.gstart[j] + t;
                if (c.gdead[midx]) continue;
                node_t v = c.plmem[midx];
                if (v == x) continue;                       /* x already in Si */
                if (!lbl_lt(W->d[v], Bi)) continue;
                if (W->siddup[v] == si_st) continue;
                W->siddup[v] = si_st;
                /* FIX-SIGROW: Si is sized from the pull count cnt, but the
                 * expansion appends one entry per surviving group member, and
                 * a group reaches up to |tree| (partition_tree only cuts when
                 * |Uv| >= s, so one child subtree can be merged whole).  With
                 * cnt << |group| the two bounds disagree and c.Si[sn++] ran
                 * off the buffer (reachable whenever L >= 2, e.g. a fixed
                 * small t via CHD_T, where Ssz grows past KMAX). */
                if (sn == c.Sicap) {
                    c.Sicap = c.Sicap * 2 + 64;
                    c.Si = (node_t *)xrealloc(c.Si, c.Sicap * sizeof(node_t));
                }
                c.Si[sn++] = v;
            }
        }
        for (uint64_t i = 0; i < sn; i++) W->siddup[c.Si[i]] = 0;
        /* BM.13: child call */
        Ret r;
        bmssp(W, Bi, c.Si, sn, level - 1, W->Lam[level - 1], &r);
        /* BM.14: merge child's D */
        dstr_merge(W, D, r.D);
        dstr_release(W, r.D);          /* child's DStr header is malloc'd */
        /* BM.15: delete U_i keys.  With zero live entries in D every delete
         * returns immediately (live_ent[v] is NONE32 or stale), so the whole
         * O(|U_i|) walk is skipped — typical of the collapsed regime where
         * the base case settles everything and D stays empty. */
        if (D->live_total)
            for (uint64_t i = 0; i < r.Un; i++) dstr_delete(W, r.U[i]);
        /* BM.16-BM.18: membership updates + J — with no groups registered
         * this call never pm_pushed, so pm_group is NONE32 for every vertex
         * and the pass is a pure no-op */
        if (c.g_n)
            for (uint64_t i = 0; i < r.Un; i++) {
                node_t u = r.U[i];
                uint32_t j = pm_group(W, &c, u);
                if (j == NONE32) continue;
                uint32_t t = W->pm_top[u];
                uint32_t midx = (t && c.pm[t - 1].owner == c.id) ? c.pm[t - 1].midx : NONE32;
                if (midx != NONE32) c.gdead[midx] = 1;
                pm_pop(W, &c, u);
                if (c.piv[j] == u) {
                    /* group may still have alive members -> reselect later */
                    int alive = 0;
                    for (uint32_t q = 0; q < c.gcnt[j]; q++)
                        if (!c.gdead[c.gstart[j] + q]) { alive = 1; break; }
                    if (alive) {
                        if (c.Jn == c.Jcap) {
                            c.Jcap = c.Jcap ? c.Jcap * 2 : 16;
                            c.J = (uint32_t *)xrealloc(c.J, c.Jcap * sizeof(uint32_t));
                        }
                        c.J[c.Jn++] = j;
                    }
                }
            }
        /* BM.19-BM.22: settle scans */
        for (uint64_t i = 0; i < r.Un; i++) {
            node_t u = r.U[i];
            node_t s = W->ptr[u], e = G->gSt[u + 1];
            /* ptr[u] == e means this vertex's static range was already
             * scanned to the end by whoever settled it (base_case commits the
             * resume pointer).  d[u] is final once settled, so re-running the
             * loop from e is a guaranteed no-op -- skip the label load and
             * the store instead. */
            if (s >= e) continue;
            Label du = W->d[u];
            const int has_del = G->ghas_del;
            PROF(8, for (; s < e; s++) {
                if (has_del && G->gdel[s]) continue;    /* Lemma L deleted */
                double clen = du.len + G->gW[s];
                if (clen > c.B.len) break;               /* len-only pre-break */
                node_t v = G->gHead[s];
                if (W->ustamp[v]) continue;
                Label cand; cand.len = clen; cand.hops = du.hops + 1; cand.eid = s;
                if (!lbl_lt(cand, c.B)) break;
                int ok = RELAX(W, v, u, cand);
                /* BM.20-21 (paper): insert only when d[u] (+) e >= B_i;
                 * vertices improved below B_i are rescued by the same
                 * iteration's BM.12 expansion (group members) or later
                 * relax re-confirmation.  Settled vertices never re-enter. */
                if (ok && !lbl_lt(cand, Bi)) {
                    dstr_insert(W, D, v, W->d[v]);
                    uint32_t j = pm_group(W, &c, v);
                    if (j != NONE32) {
                        int inJ = 0;
                        for (uint32_t q = 0; q < c.Jn; q++) if (c.J[q] == j) { inJ = 1; break; }
                        if (!inJ && lbl_lt(W->d[v], W->d[c.piv[j]]))
                            c.piv[j] = v;               /* BM.22 pivot switch */
                    }
                }
            });
            W->ptr[u] = s;
        }
        /* BM.23: reselect pivots of J */
        for (uint32_t q = 0; q < c.Jn; q++) {
            uint32_t j = c.J[q];
            node_t best = NODE_MAX; Label bd = LBL_INF;
            for (uint32_t t = 0; t < c.gcnt[j]; t++) {
                uint32_t midx = c.gstart[j] + t;
                if (c.gdead[midx]) continue;
                node_t v = c.plmem[midx];
                if (lbl_lt(W->d[v], bd)) { bd = W->d[v]; best = v; }
            }
            if (best != NODE_MAX) {
                c.piv[j] = best;
                dstr_insert(W, D, best, W->d[best]);
            }
        }
        /* BM.24 */
        Bp = r.Bp;
        for (uint64_t i = 0; i < r.Un; i++) call_U_append(W, &c, r.U[i]);
        upool_recycle(W, r.U, r.Ucap);
        c.Jn = 0;
    }

    /* BM.24a */
    if (dstr_isempty(W, D)) Bp = c.B;

    /* BM.25: leftover S above B' */
    for (uint64_t i = 0; i < Ssz; i++) {
        node_t x = S[i];
        if (lbl_le(Bp, W->d[x]) && lbl_lt(W->d[x], c.B))
            dstr_insert(W, D, x, W->d[x]);
    }

    /* BM.26-BM.29 */
    {
        if (c.Wpcap < (uint64_t)c.Wn + 8) {
            c.Wpcap = ((uint64_t)c.Wn + 8) * 2;
            c.Wp = (node_t *)xrealloc(c.Wp, c.Wpcap * sizeof(node_t));
        }
        uint64_t wn = 0;
        for (uint32_t i = 0; i < c.Wn; i++) {
            node_t x = c.W[i];
            if (W->ustamp[x] == c.id) continue;          /* in U */
            if (!lbl_lt(W->d[x], Bp)) continue;
            c.Wp[wn++] = x;
        }
        for (uint64_t i = 0; i < wn; i++) {
            node_t u = c.Wp[i];
            node_t s = W->ptr[u], e = G->gSt[u + 1];
            if (s >= e) continue;                  /* range already exhausted */
            Label du = W->d[u];
            const int has_del = G->ghas_del;
            PROF(13, for (; s < e; s++) {
                if (has_del && G->gdel[s]) continue;    /* Lemma L deleted */
                double clen = du.len + G->gW[s];
                if (clen > c.B.len) break;               /* len-only pre-break */
                node_t v = G->gHead[s];
                if (W->ustamp[v]) continue;
                Label cand; cand.len = clen; cand.hops = du.hops + 1; cand.eid = s;
                if (!lbl_lt(cand, c.B)) break;
                int ok = RELAX(W, v, u, cand);
                if (ok && !lbl_lt(cand, Bp))        /* BM.28 (ok => unsettled) */
                    dstr_insert(W, D, v, W->d[v]);
            });
            W->ptr[u] = s;
        }
        for (uint64_t i = 0; i < wn; i++) dstr_delete(W, c.Wp[i]);  /* BM.29 */
        for (uint64_t i = 0; i < wn; i++) call_U_append(W, &c, c.Wp[i]);
    }

    /* BM.30: pop this call's remaining P-entries */
    if (c.g_n) {
        for (uint32_t j = 0; j < c.g_n; j++)
            for (uint32_t t = 0; t < c.gcnt[j]; t++) {
                uint32_t midx = c.gstart[j] + t;
                if (!c.gdead[midx]) pm_pop(W, &c, c.plmem[midx]);
            }
    }

    ret->Bp = Bp;
    ret->U = c.U; ret->Un = c.Un; ret->Ucap = c.Ucap;
    {
        DStr *pd = dstr_alloc(W, 0, LBL_INF);
        *pd = c.D;
        ret->D = pd;
    }
    /* c.U and c.D ownership transferred; zero to avoid double free */
    c.U = NULL;
    c.D.blist = NULL;
    call_free(W, &c);
}

/* ------------------------------------------------------------------ */
/* Driver: workspace setup, top call, output map-back (P5)             */
/* ------------------------------------------------------------------ */

static void chd_free_workspace(Chd *W) {
    free(W->g.gSt); free(W->g.gHead); free(W->g.gW); free(W->g.gdel);
    free(W->g.gRep); free(W->g.orig);
    free(W->kid);
    free(W->d); free(W->ptr); free(W->pred);
    free(W->live_ent);
    free(W->fmark); free(W->kst); free(W->treeof);
    free(W->wstamp); free(W->inSst); free(W->inQst); free(W->asgst);
    free(W->ustamp); free(W->pm_top); free(W->hpos); free(W->siddup);
    free(W->tparent); free(W->tedge);
    free(W->Mtab); free(W->Lam);
    free(W->ent); free(W->blk); free(W->sc);
    if (W->fpb) {
        free(W->fpb->tv); free(W->fpb->thead); free(W->fpb->tcnt);
        free(W->fpb->H); free(W->fpb->K); free(W->fpb->kpar); free(W->fpb->kedge);
        free(W->fpb->Q);
        free(W->fpb);
        W->fpb = NULL;
    }
    /* release the hot-path scratch pools */
    free(W->ih_key); free(W->ih_id);
    free(W->pull_consumed); free(W->merge_nb);
    for (uint32_t i = 0; i < W->dstr_pool_n; i++) free(W->dstr_pool[i]);
    free(W->dstr_pool);
    for (uint32_t i = 0; i < W->upool_n; i++) free(W->upool[i]);
    free(W->upool); free(W->ucap);
    /* NOTE: no struct-wide memset here — chd_run() memsets on entry, and
     * wiping now would destroy the statistics chd_sssp copies afterwards. */
}

static void chd_setup_workspace(Chd *W) {
    node_t N = W->g.N;
    size_t sz = (size_t)(N ? N : 1);
    W->d        = (Label *)xrealloc(W->d, sz * sizeof(Label));
    W->ptr      = (uint32_t *)xrealloc(W->ptr, sz * sizeof(uint32_t));
    W->pred     = (uint32_t *)xrealloc(W->pred, sz * sizeof(uint32_t));
    W->live_ent = (uint32_t *)xrealloc(W->live_ent, sz * sizeof(uint32_t));
    W->fmark    = (uint32_t *)calloc(sz, sizeof(uint32_t));
    W->kst      = (uint32_t *)calloc(sz, sizeof(uint32_t));
    W->treeof   = (uint32_t *)calloc(sz, sizeof(uint32_t));
    W->wstamp   = (uint32_t *)calloc(sz, sizeof(uint32_t));
    W->inSst    = (uint32_t *)calloc(sz, sizeof(uint32_t));
    W->inQst    = (uint32_t *)calloc(sz, sizeof(uint32_t));
    W->asgst    = (uint32_t *)calloc(sz, sizeof(uint32_t));
    W->ustamp   = (uint32_t *)calloc(sz, sizeof(uint32_t));
    W->pm_top   = (uint32_t *)calloc(sz, sizeof(uint32_t));
    W->hpos     = (uint32_t *)calloc(sz, sizeof(uint32_t));
    W->siddup   = (uint32_t *)calloc(sz, sizeof(uint32_t));
    W->tparent  = (int32_t *)xrealloc(W->tparent, sz * sizeof(int32_t));
    W->tedge    = (uint32_t *)xrealloc(W->tedge, sz * sizeof(uint32_t));
    memset(W->tparent, 0xFF, sz * sizeof(int32_t));   /* -1 everywhere */
    memset(W->tedge, 0xFF, sz * sizeof(uint32_t));    /* EID_NONE = ~0u  */
    /* bulk init: ptr mirrors gSt (node_t == uint32_t), pred/live_ent are
     * all-ones sentinels; only d needs the per-element LBL_INF pattern */
    memcpy(W->ptr, W->g.gSt, sz * sizeof(uint32_t));
    memset(W->pred, 0xFF, sz * sizeof(uint32_t));         /* NODE_MAX    */
    memset(W->live_ent, 0xFF, sz * sizeof(uint32_t));     /* NONE32      */
    for (node_t i = 0; i < N; i++) W->d[i] = LBL_INF;
    /* presize the shared base-case heap: level-0 calls are depth-first and
     * single-active, and the heap can legitimately grow to N entries */
    if (W->ih_cap < (uint64_t)N + 1) {
        W->ih_cap = (uint64_t)N + 1;
        W->ih_key = (Label *)xrealloc(W->ih_key, (W->ih_cap + 1) * sizeof(Label));
        W->ih_id  = (node_t *)xrealloc(W->ih_id,  (W->ih_cap + 1) * sizeof(node_t));
    }
}

static int chd_run(Chd *W, const CSRGraph *g, node_t src, weight_t *dist, node_t *pred) {
    node_t n = g->n;
    memset(W, 0, sizeof(*W));

    PROF(0, chd_preprocess(W, g, src));
    chd_params(W, W->g.N, W->g.gM);
    chd_setup_workspace(W);

    node_t xs = W->g.gRep[W->kid[src]];
    W->d[xs].len = 0.0; W->d[xs].hops = 0; W->d[xs].eid = EID_NONE;

    if (W->g.gM > 0) {
        node_t S0[1]; S0[0] = xs;
        Ret r;
        PROF(1, bmssp(W, LBL_INF, S0, 1, W->L, W->Lam[W->L], &r));
        if (r.U) upool_recycle(W, r.U, r.Ucap);
        dstr_release(W, r.D);
    }

    /* P5: map virtual labels back to original vertices */
    PROF(9, for (node_t v = 0; v < n; v++) {
        node_t kv = W->kid[v];
        if (kv == NONE32) { dist[v] = WEIGHT_INF; pred[v] = NODE_MAX; continue; }
        node_t x = W->g.gRep[kv];
        dist[v] = W->d[x].len;
        pred[v] = (dist[v] == WEIGHT_INF) ? NODE_MAX : (node_t)W->pred[x];
    });
    chd_free_workspace(W);
    return 0;
}

/* last-run statistics, exposed for the benchmark driver */
static Chd g_last_stats;
uint64_t chd_last_stat(int which); /* fwd */

int chd_sssp(const CSRGraph *g, node_t src, weight_t *dist, node_t *pred) {
    if (!chd_dispatch_core(g->n, g->m)) {
        bellman_ford_sssp(g, src, dist, pred);
        return 1; /* fallback used */
    }
    Chd W;
    int rc = chd_run(&W, g, src, dist, pred);
    g_last_stats = W;  /* stats only; heavy arrays were freed */
    prof_dump();
    return rc;
}

int chd_sssp_force_core(const CSRGraph *g, node_t src, weight_t *dist, node_t *pred) {
    Chd W;
    int rc = chd_run(&W, g, src, dist, pred);
    g_last_stats = W;
    return rc;
}

void chd_set_t_override(uint32_t t) {
    g_chd_t_override = t;
}

uint64_t chd_last_stat(int which) {
    switch (which) {
        case 0: return g_last_stats.stat_calls;
        case 1: return g_last_stats.stat_base_calls;
        case 2: return g_last_stats.stat_fp_invoc;
        case 3: return g_last_stats.stat_fp_searches;
        case 4: return g_last_stats.stat_deleted;
        case 5: return g_last_stats.stat_inserts;
        case 6: return g_last_stats.stat_pulls;
        case 7: return g_last_stats.stat_merge_blks;
        default: return 0;
    }
}
