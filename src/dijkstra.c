#include "../include/chd.h"
#include <stdlib.h>

/* Reference Dijkstra, O(m + n log n): indexed 4-ary heap.
 * This is the honest comparison baseline (same one used by DMMSY-SSSP). */

typedef struct { weight_t v; node_t i; } HeapNode;
typedef struct {
    HeapNode *nodes; /* 1-indexed */
    node_t   *pos;   /* 0 = absent */
    node_t   n;
} Heap4;

static void h4_init(Heap4 *h, node_t n) {
    h->nodes = (HeapNode *)malloc(sizeof(HeapNode) * (n + 1));
    h->pos   = (node_t *)calloc(n, sizeof(node_t));
    h->n     = n;
}
static void h4_free(Heap4 *h) { free(h->nodes); free(h->pos); }

static void h4_up(Heap4 *h, node_t i) {
    HeapNode x = h->nodes[i];
    while (i > 1) {
        node_t p = (i - 2) / 4 + 1;
        if (h->nodes[p].v <= x.v) break;
        h->nodes[i] = h->nodes[p]; h->pos[h->nodes[i].i] = i; i = p;
    }
    h->nodes[i] = x; h->pos[x.i] = i;
}

static void h4_down(Heap4 *h, node_t i, node_t sz) {
    HeapNode x = h->nodes[i];
    for (;;) {
        node_t c = i * 4 - 2, best = c; weight_t bv;
        if (c > sz) break;
        bv = h->nodes[c].v;
        for (node_t k = 1; k <= 3 && c + k <= sz; k++)
            if (h->nodes[c + k].v < bv) { best = c + k; bv = h->nodes[best].v; }
        if (x.v <= bv) break;
        h->nodes[i] = h->nodes[best]; h->pos[h->nodes[i].i] = i; i = best;
    }
    h->nodes[i] = x; h->pos[x.i] = i;
}

static void h4_push(Heap4 *h, node_t *sz, node_t v, weight_t d) {
    node_t p = h->pos[v];
    node_t i;
    if (p == 0) { i = ++(*sz); }
    else { i = p; if (d >= h->nodes[i].v) return; }
    h->nodes[i].v = d; h->nodes[i].i = v;
    h4_up(h, i);
}

static void h4_pop(Heap4 *h, node_t *sz, node_t *v, weight_t *d) {
    *v = h->nodes[1].i; *d = h->nodes[1].v;
    h->pos[*v] = 0;
    if (*sz == 1) { (*sz)--; return; }
    h->nodes[1] = h->nodes[(*sz)--];
    h->pos[h->nodes[1].i] = 1;
    h4_down(h, 1, *sz);
}

void dijkstra_ref(const CSRGraph *g, node_t src, weight_t *dist, node_t *pred) {
    node_t n = g->n;
    for (node_t i = 0; i < n; i++) { dist[i] = WEIGHT_INF; if (pred) pred[i] = NODE_MAX; }
    if (n == 0) return;
    dist[src] = 0.0;

    Heap4 h; h4_init(&h, n);
    node_t sz = 0;
    h4_push(&h, &sz, src, 0.0);
    while (sz) {
        node_t u; weight_t du;
        h4_pop(&h, &sz, &u, &du);
        if (du > dist[u]) continue;
        for (node_t i = g->offset[u]; i < g->offset[u + 1]; i++) {
            node_t v = g->edges[i].v;
            weight_t nd = du + g->edges[i].w;
            if (nd < dist[v]) { dist[v] = nd; if (pred) pred[v] = u; h4_push(&h, &sz, v, nd); }
        }
    }
    h4_free(&h);
}
