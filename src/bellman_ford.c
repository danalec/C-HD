#include "../include/chd.h"
#include <stdlib.h>
#include <string.h>

/* Verified Bellman-Ford fallback (paper SS dispatch / BF.prog):
 * O((n+1)(m+1)) worst-case, exact for non-negative (and arbitrary) weights.
 * Plain row-scan with early termination on a clean pass. */

void bellman_ford_sssp(const CSRGraph *g, node_t src, weight_t *dist, node_t *pred) {
    node_t n = g->n;
    for (node_t i = 0; i < n; i++) { dist[i] = WEIGHT_INF; pred[i] = NODE_MAX; }
    if (n == 0) return;
    dist[src] = 0.0;

    /* relaxation order: ascending vertex id, early-exit when a full pass
       relaxes nothing.  Worst case n-1 passes. */
    for (node_t pass = 0; pass + 1 < n; pass++) {
        int changed = 0;
        for (node_t u = 0; u < n; u++) {
            weight_t du = dist[u];
            if (du == WEIGHT_INF) continue;
            for (node_t i = g->offset[u]; i < g->offset[u + 1]; i++) {
                node_t v = g->edges[i].v;
                weight_t nd = du + g->edges[i].w;
                if (nd < dist[v]) { dist[v] = nd; pred[v] = u; changed = 1; }
            }
        }
        if (!changed) break;
    }
    (void)src;
}
