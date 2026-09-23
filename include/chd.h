#ifndef CHD_COMMON_H
#define CHD_COMMON_H

/*
 * C-HD: high-performance C implementation of the Concise Heuristic
 * Decomposition SSSP algorithm (directed graphs, non-negative real weights).
 *
 * Reference: "PAPER_CHD v2.0" (Frontier.CHD.Final, Lean-verified):
 *   T(n,m) = O(n + m + m*lg(2 + m/(n+1)) + m^{1/3} * (n*lg(n+2))^{2/3})
 * certified for m <= n * floor(floor(log2 n)^{3/4}); Bellman-Ford fallback
 * otherwise.  See README.md for the full algorithm map (P1-P5, FH.1-26,
 * MP.1-10, BM.1-31, BC.1-9).
 */

#include <stdint.h>
#include <stdbool.h>

typedef uint32_t node_t;
typedef double   weight_t;

/* Infinity equivalent for double */
#ifndef WEIGHT_INF
#include <math.h>
#define WEIGHT_INF ((weight_t)HUGE_VAL)
#endif
#define NODE_MAX ((node_t)-1)

typedef struct {
    node_t   v;
    weight_t w;
} Edge;

/* CSR graph */
typedef struct {
    node_t   n;
    node_t   m;
    node_t  *offset;   /* size n + 1            */
    Edge    *edges;    /* size m                */
    weight_t mean_weight;
} CSRGraph;

/* ---------------- graph generation / utilities ---------------- */
CSRGraph random_graph(node_t n, node_t m, weight_t max_w, uint64_t seed);
CSRGraph grid_graph(node_t side, weight_t max_w, uint64_t seed); /* sparse, m ~ 2n */
void     free_graph(CSRGraph *g);
int      graph_equal_dist(const weight_t *a, const weight_t *b, node_t n);

/* ---------------- timing ---------------- */
double now_seconds(void); /* monotonic, platform independent */
void   cpu_model(char *out, size_t cap);

/* ---------------- SSSP APIs ---------------- */
/* Reference O(m + n log n) Dijkstra with 4-ary heap (comparison baseline). */
void dijkstra_ref(const CSRGraph *g, node_t src, weight_t *dist, node_t *pred);

/* Verified fallback: plain Bellman-Ford, O((n+1)(m+1)) worst case. */
void bellman_ford_sssp(const CSRGraph *g, node_t src, weight_t *dist, node_t *pred);

/*
 * C-HD dispatcher (paper SS.1/Sec.6): runs the C-HD core when
 *   log2(n) >= 16  and  ceil(m/n) <= floor(floor(log2 n)^{3/4}),
 * Bellman-Ford otherwise.  dist/pred must have room for n entries.
 * Returns 0 on success.
 */
int  chd_sssp(const CSRGraph *g, node_t src, weight_t *dist, node_t *pred);

/* Test hook: force the C-HD core regardless of the dispatcher window.
 * Correct for every input (any parameter values keep exactness); used by
 * the test-suite to exercise the core on small graphs. */
int  chd_sssp_force_core(const CSRGraph *g, node_t src, weight_t *dist, node_t *pred);

/* Tunable override for the paper parameter t (0 = paper default). */
void chd_set_t_override(uint32_t t);

/* Last-run statistics (benchmark/diagnostics).  which: 0=calls 1=base_calls
   2=fp_invocations 3=fp_searches 4=deleted_edges 5=ds_inserts 6=pulls
   7=merged_blocks */
uint64_t chd_last_stat(int which);

#endif /* CHD_COMMON_H */
