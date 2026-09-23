/*
 * test_chd.c — correctness suite for the C-HD implementation.
 *
 * Every case is checked against the reference Dijkstra on distances, and the
 * predecessor tree is validated edge-by-edge (dist[v] == dist[pred] + w).
 * Both the forced C-HD core (exercises the recursion even on tiny graphs)
 * and the natural dispatcher path are covered.
 */

#include "../include/chd.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

static int g_fail = 0;
static int g_checks = 0;

static void fail(const char *what, node_t n, node_t m, uint64_t seed, node_t v,
                 weight_t got, weight_t want) {
    printf("FAIL [%s] n=%u m=%u seed=%llu v=%u got=%.17g want=%.17g\n",
           what, n, m, (unsigned long long)seed, v, got, want);
    g_fail++;
    if (g_fail > 20) { printf("too many failures, aborting\n"); exit(1); }
}

/* validate pred: for every reachable v != src, dist[v] == dist[pred] + minw(pred->v) */
static int check_pred(const CSRGraph *g, node_t src, const weight_t *dist, const node_t *pred) {
    for (node_t v = 0; v < g->n; v++) {
        if (v == src) { if (dist[v] != 0.0) return 0; continue; }
        if (dist[v] == WEIGHT_INF) { if (pred[v] != NODE_MAX) return 0; continue; }
        node_t p = pred[v];
        if (p == NODE_MAX || p >= g->n) return 0;
        if (dist[p] == WEIGHT_INF) return 0;
        weight_t best = WEIGHT_INF;
        for (node_t i = g->offset[p]; i < g->offset[p + 1]; i++)
            if (g->edges[i].v == v && g->edges[i].w < best) best = g->edges[i].w;
        if (best == WEIGHT_INF) return 0;               /* no such edge */
        if (fabs(dist[p] + best - dist[v]) > 1e-9 * (1.0 + fabs(dist[v]))) return 0;
        /* cycle guard: pred chain must reach src within n steps */
    }
    /* cycle detection */
    {
        node_t *state = (node_t *)calloc(g->n, sizeof(node_t));
        node_t gen = 0;
        for (node_t v = 0; v < g->n; v++) {
            if (dist[v] == WEIGHT_INF || v == src) continue;
            node_t u = v; int steps = 0;
            gen++;
            while (u != src && state[u] != gen && steps <= (int)g->n) { state[u] = gen; u = pred[u]; steps++; }
            if (u != src) { free(state); return 0; }
        }
        free(state);
    }
    return 1;
}

static void run_case(const char *tag, const CSRGraph *g, node_t src, int force_core,
                     uint64_t seed) {
    node_t n = g->n;
    weight_t *d_ref = (weight_t *)malloc(n * sizeof(weight_t));
    weight_t *d_chd = (weight_t *)malloc(n * sizeof(weight_t));
    node_t *p_chd = (node_t *)malloc(n * sizeof(node_t));
    dijkstra_ref(g, src, d_ref, NULL);

    if (force_core) chd_sssp_force_core(g, src, d_chd, p_chd);
    else chd_sssp(g, src, d_chd, p_chd);
    g_checks++;

    if (!graph_equal_dist(d_ref, d_chd, n)) {
        for (node_t v = 0; v < n; v++)
            if (!graph_equal_dist(d_ref + v, d_chd + v, 1)) {
                fail(tag, n, g->m, seed, v, d_chd[v], d_ref[v]);
                break;
            }
    }
    if (!check_pred(g, src, d_chd, p_chd)) {
        printf("FAIL [pred] tag=%s n=%u m=%u seed=%llu\n", tag, n, g->m, (unsigned long long)seed);
        g_fail++;
    }
    free(d_ref); free(d_chd); free(p_chd);
}

/* hand-built graph from edge list */
static CSRGraph make_graph(node_t n, const int *edges_triplets, int count) {
    node_t *cnt = (node_t *)calloc(n, sizeof(node_t));
    for (int i = 0; i < count; i++) cnt[edges_triplets[i * 3]]++;
    CSRGraph g; g.n = n; g.m = (node_t)count;
    g.offset = (node_t *)malloc((n + 1) * sizeof(node_t));
    g.edges = (Edge *)malloc((count ? count : 1) * sizeof(Edge));
    g.offset[0] = 0;
    for (node_t i = 0; i < n; i++) g.offset[i + 1] = g.offset[i] + cnt[i];
    memset(cnt, 0, n * sizeof(node_t));
    weight_t sum = 0;
    for (int i = 0; i < count; i++) {
        node_t u = (node_t)edges_triplets[i * 3];
        node_t idx = g.offset[u] + cnt[u]++;
        g.edges[idx].v = (node_t)edges_triplets[i * 3 + 1];
        g.edges[idx].w = (weight_t)edges_triplets[i * 3 + 2];
        sum += g.edges[idx].w;
    }
    g.mean_weight = count ? sum / count : 0;
    free(cnt);
    return g;
}

static void test_handbuilt(void) {
    fprintf(stderr, "[t] handbuilt start\n");
    /* chain 0->1->2->3 */
    { int e[] = {0,1,2, 1,2,3, 2,3,4}; CSRGraph g = make_graph(4, e, 3);
      fprintf(stderr, "[t] chain made\n");
      run_case("chain", &g, 0, 1, 0); run_case("chain-disp", &g, 0, 0, 0); free_graph(&g); }
    /* disconnected */
    { int e[] = {0,1,1, 2,3,1}; CSRGraph g = make_graph(4, e, 2);
      run_case("disc", &g, 0, 1, 0); free_graph(&g); }
    /* parallel edges + self loops */
    { int e[] = {0,1,5, 0,1,2, 0,0,0, 1,1,0, 1,2,1}; CSRGraph g = make_graph(3, e, 5);
      run_case("par", &g, 0, 1, 0); free_graph(&g); }
    /* zero-weight cycle 0->1->2->0 */
    { int e[] = {0,1,0, 1,2,0, 2,0,0, 0,3,7}; CSRGraph g = make_graph(4, e, 4);
      run_case("zerocycle", &g, 0, 1, 0); free_graph(&g); }
    /* single vertex, no edges */
    { CSRGraph g = make_graph(1, NULL, 0);
      run_case("single", &g, 0, 1, 0); free_graph(&g); }
    /* source with only in-edges */
    { int e[] = {1,0,3, 0,2,1}; CSRGraph g = make_graph(3, e, 2);
      run_case("outonly", &g, 0, 1, 0); free_graph(&g); }
    /* two vertices, one edge */
    { int e[] = {0,1,4}; CSRGraph g = make_graph(2, e, 1);
      run_case("two", &g, 0, 1, 0); run_case("two-src1", &g, 1, 1, 0); free_graph(&g); }
    /* diamond with ties */
    { int e[] = {0,1,1, 0,2,1, 1,3,1, 2,3,1}; CSRGraph g = make_graph(4, e, 4);
      run_case("diamond", &g, 0, 1, 0); free_graph(&g); }
    printf("[handbuilt] done\n");
}

static void test_random(void) {
    static const node_t sizes[] = {2, 3, 5, 8, 13, 30, 77, 200, 555, 1000, 4096, 20000};
    for (unsigned si = 0; si < sizeof(sizes)/sizeof(sizes[0]); si++) {
        node_t n = sizes[si];
        for (int rep = 0; rep < 6; rep++) {
            uint64_t seed = 0xC0FFEE + si * 131 + rep;
            int variant = rep % 3;
            node_t m;
            if (variant == 0) m = n * 1 + 7;         /* tree-ish */
            else if (variant == 1) m = n * 3 + 13;   /* moderate */
            else m = n * 10 + 29;                    /* denser (outside window when forced) */
            CSRGraph g = random_graph(n, m, 100.0, seed);
            node_t src = (node_t)(seed % n);
            run_case("rand-core", &g, src, 1, seed);
            if (rep == 0 && n <= 4096) run_case("rand-disp", &g, src, 0, seed);
            free_graph(&g);
        }
        printf("[random] n=%u ok\n", n);
    }
}

/* zero-weight-heavy graphs (exercise hop tie-breaking) */
static void test_zero_weights(void) {
    for (int rep = 0; rep < 10; rep++) {
        uint64_t seed = 777 + rep;
        node_t n = 500;
        node_t m = 4 * n;
        CSRGraph g = random_graph(n, m, 0.0, seed); /* all zero weights */
        for (node_t i = 0; i < m; i++) g.edges[i].w = 0.0;
        run_case("zeroW", &g, (node_t)(rep * 37 % n), 1, seed);
        free_graph(&g);
    }
    /* mixed zero/nonzero */
    for (int rep = 0; rep < 10; rep++) {
        uint64_t seed = 4242 + rep;
        node_t n = 800;
        CSRGraph g = random_graph(n, n * 6, 10.0, seed);
        for (node_t i = 0; i < g.m; i += 3) g.edges[i].w = 0.0;
        run_case("mixedW", &g, (node_t)(rep * 91 % n), 1, seed);
        free_graph(&g);
    }
    printf("[zero-weights] done\n");
}

/* dispatcher-boundary sizes: the C-HD branch runs naturally (lg2 n >= 16) */
static void test_dispatch_window(void) {
    node_t sizes[] = {65536, 100000, 262144};
    for (unsigned si = 0; si < 3; si++) {
        node_t n = sizes[si];
        for (int rep = 0; rep < 2; rep++) {
            uint64_t seed = 0xBEEF + si * 17 + rep;
            node_t m = n * (4 + rep * 3);            /* 4n and 7n: inside window */
            CSRGraph g = random_graph(n, m, 100.0, seed);
            run_case("disp-win", &g, (node_t)(seed % n), 0, seed);
            run_case("disp-win-core", &g, (node_t)(seed % n), 1, seed);
            free_graph(&g);
        }
        printf("[dispatch] n=%u ok\n", n);
    }
}

/* larger forced-core run (multi-level recursion, L >= 2 needs N >= 2^16) */
static void test_large_forced(void) {
    uint64_t seed = 0x5EED;
    node_t n = 300000;
    node_t m = 8 * n;
    CSRGraph g = random_graph(n, m, 100.0, seed);
    run_case("large-core", &g, 12345, 1, seed);
    free_graph(&g);
    printf("[large-forced] n=%u ok\n", n);
}

/* determinism: same input twice -> identical output */
static void test_determinism(void) {
    uint64_t seed = 0xD00D;
    node_t n = 50000, m = 6 * n;
    CSRGraph g = random_graph(n, m, 50.0, seed);
    weight_t *d1 = (weight_t *)malloc(n * sizeof(weight_t));
    weight_t *d2 = (weight_t *)malloc(n * sizeof(weight_t));
    node_t *p1 = (node_t *)malloc(n * sizeof(node_t));
    node_t *p2 = (node_t *)malloc(n * sizeof(node_t));
    chd_sssp_force_core(&g, 7, d1, p1);
    chd_sssp_force_core(&g, 7, d2, p2);
    if (memcmp(d1, d2, n * sizeof(weight_t)) != 0 || memcmp(p1, p2, n * sizeof(node_t)) != 0) {
        printf("FAIL [determinism]\n"); g_fail++;
    }
    free(d1); free(d2); free(p1); free(p2);
    free_graph(&g);
    printf("[determinism] done\n");
}

int main(void) {
    setvbuf(stdout, NULL, _IONBF, 0);
    setvbuf(stderr, NULL, _IONBF, 0);
    printf("[start]\n");
    double t0 = now_seconds();
    test_handbuilt();
    test_random();
    test_zero_weights();
    test_dispatch_window();
    test_determinism();
    test_large_forced();
    double t1 = now_seconds();
    printf("----------------------------------------\n");
    printf("checks: %d   failures: %d   time: %.2fs\n", g_checks, g_fail, t1 - t0);
    return g_fail ? 1 : 0;
}
