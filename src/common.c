#include "../include/chd.h"
#include <math.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#if defined(_WIN32)
#include <windows.h>
#pragma comment(lib, "advapi32.lib")
#else
#include <unistd.h>
#endif

/* xorshift64* — deterministic, fast, independent of libc rand() */
typedef struct { uint64_t s; } Rng;
static inline uint64_t rng_next(Rng *r) {
    uint64_t x = r->s;
    x ^= x >> 12; x ^= x << 25; x ^= x >> 27;
    r->s = x;
    return x * 0x2545F4914F6CDD1DULL;
}
static inline double rng_double(Rng *r) { /* [0,1) */
    return (double)(rng_next(r) >> 11) * (1.0 / 9007199254740992.0);
}
static inline node_t rng_below(Rng *r, node_t n) {
    /* n == 0 is a valid (degenerate) graph size -- dijkstra_ref and
     * chd_preprocess both accept it -- so the helper must not divide by it. */
    return n ? (node_t)(rng_next(r) % n) : 0u;
}

/* ---------------- timing ---------------- */
double now_seconds(void) {
#if defined(_WIN32)
    LARGE_INTEGER f, c;
    QueryPerformanceFrequency(&f);
    QueryPerformanceCounter(&c);
    return (double)c.QuadPart / (double)f.QuadPart;
#else
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
#endif
}

void cpu_model(char *out, size_t cap) {
#if defined(_WIN32)
    HKEY k;
    if (RegOpenKeyExA(HKEY_LOCAL_MACHINE,
                      "HARDWARE\\DESCRIPTION\\System\\CentralProcessor\\0",
                      0, KEY_READ, &k) == ERROR_SUCCESS) {
        char buf[256] = {0};
        DWORD len = sizeof(buf) - 1, type = REG_SZ;
        if (RegQueryValueExA(k, "ProcessorNameString", 0, &type,
                             (LPBYTE)buf, &len) == ERROR_SUCCESS) {
            /* trim trailing spaces */
            while (len > 0 && (buf[len-1] == ' ' || buf[len-1] == '\0')) buf[--len] = 0;
            strncpy(out, buf, cap - 1);
            out[cap-1] = 0;
            RegCloseKey(k);
            return;
        }
        RegCloseKey(k);
    }
#endif
    strncpy(out, "unknown CPU", cap - 1);
    out[cap-1] = 0;
}

/* ---------------- graph generation ---------------- */
CSRGraph random_graph(node_t n, node_t m, weight_t max_w, uint64_t seed) {
    Rng rng = { seed ? seed : 0x9E3779B97F4A7C15ULL };
    CSRGraph g;
    g.n = n; g.m = m;
    g.offset = (node_t *)calloc(n + 1, sizeof(node_t));
    g.edges  = (Edge *)malloc(sizeof(Edge) * (m ? m : 1));

    typedef struct { node_t u, v; weight_t w; } TE;
    TE *te = (TE *)malloc(sizeof(TE) * (m ? m : 1));
    for (node_t i = 0; i < m; i++) {
        node_t u = rng_below(&rng, n);
        node_t v = rng_below(&rng, n);
        /* +1 keeps weights away from exact 0 by default; zero-weight
           regimes are tested separately by the test-suite. */
        te[i].u = u; te[i].v = v;
        te[i].w = 1.0 + rng_double(&rng) * max_w;
        g.offset[u + 1]++;
    }
    for (node_t i = 0; i < n; i++) g.offset[i + 1] += g.offset[i];
    node_t *cur = (node_t *)calloc(n, sizeof(node_t));
    weight_t sum = 0.0;
    for (node_t i = 0; i < m; i++) {
        node_t idx = g.offset[te[i].u] + cur[te[i].u]++;
        g.edges[idx].v = te[i].v;
        g.edges[idx].w = te[i].w;
        sum += te[i].w;
    }
    free(cur); free(te);
    g.mean_weight = m ? sum / (weight_t)m : 0.0;
    return g;
}

/* undirected-grid-like sparse digraph: vertex (i,j) -> right and down,
   plus a few random long links to keep it strongly connected-ish. */
CSRGraph grid_graph(node_t side, weight_t max_w, uint64_t seed) {
    Rng rng = { seed ? seed : 0x9E3779B97F4A7C15ULL };
    node_t n = side * side;
    node_t m = 0;
    node_t *cnt = (node_t *)calloc(n, sizeof(node_t));
    for (node_t j = 0; j < side; j++)
        for (node_t i = 0; i < side; i++) {
            node_t u = j * side + i;
            if (i + 1 < side) { cnt[u]++; m++; }
            if (j + 1 < side) { cnt[u]++; m++; }
        }
    node_t extra = n / 4; m += extra;
    for (node_t i = 0; i < extra; i++) cnt[rng_below(&rng, n)]++;

    CSRGraph g; g.n = n; g.m = m;
    g.offset = (node_t *)malloc(sizeof(node_t) * (n + 1));
    g.edges  = (Edge *)malloc(sizeof(Edge) * m);
    g.offset[0] = 0;
    for (node_t i = 0; i < n; i++) g.offset[i + 1] = g.offset[i] + cnt[i];
    memset(cnt, 0, sizeof(node_t) * n);
    weight_t sum = 0.0;
    for (node_t j = 0; j < side; j++)
        for (node_t i = 0; i < side; i++) {
            node_t u = j * side + i;
            if (i + 1 < side) {
                node_t idx = g.offset[u] + cnt[u]++;
                g.edges[idx].v = u + 1;
                g.edges[idx].w = 1.0 + rng_double(&rng) * max_w; sum += g.edges[idx].w;
            }
            if (j + 1 < side) {
                node_t idx = g.offset[u] + cnt[u]++;
                g.edges[idx].v = u + side;
                g.edges[idx].w = 1.0 + rng_double(&rng) * max_w; sum += g.edges[idx].w;
            }
        }
    for (node_t i = 0; i < extra; i++) {
        node_t u = rng_below(&rng, n);
        node_t idx = g.offset[u] + cnt[u]++;
        g.edges[idx].v = rng_below(&rng, n);
        g.edges[idx].w = 1.0 + rng_double(&rng) * max_w; sum += g.edges[idx].w;
    }
    free(cnt);
    g.mean_weight = m ? sum / (weight_t)m : 0.0;
    return g;
}

void free_graph(CSRGraph *g) {
    free(g->offset); g->offset = NULL;
    free(g->edges);  g->edges  = NULL;
    g->n = g->m = 0;
}

int graph_equal_dist(const weight_t *a, const weight_t *b, node_t n) {
    for (node_t i = 0; i < n; i++) {
        if (a[i] == b[i]) continue;
        if (a[i] == WEIGHT_INF || b[i] == WEIGHT_INF) return 0;
        if (a[i] < b[i] * (1 - 1e-9) || a[i] > b[i] * (1 + 1e-9)) {
            /* absolute slack for tiny distances */
            weight_t d = a[i] - b[i]; if (d < 0) d = -d;
            if (d > 1e-9 * (1.0 + (a[i] > 0 ? a[i] : -a[i]))) return 0;
        }
    }
    return 1;
}
