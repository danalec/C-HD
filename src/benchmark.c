/*
 * benchmark.c — honest head-to-head: C-HD vs DMMSY vs Dijkstra.
 *
 * Methodology (deliberately conservative, no hardware-specific tuning):
 *   - one seeded random graph per (n, density) cell, shared by all algos;
 *   - every algo is verified against dijkstra_ref on the same run;
 *   - R timed repetitions per algo, INTERLEAVED round-robin (chd, dmmsy,
 *     dijkstra) so thermal/cache state affects all candidates equally;
 *   - report min and median; min is the least noise-contaminated estimator
 *     of true algorithmic cost, median shows typical behavior.
 *   - plain /O2 without /arch:ISA — no cache-aware or CPU-model-specific
 *     optimization is applied to either implementation.
 */

#include "../include/chd.h"
#include "dmmsy_port.h"
/* dmmsy_port.h renames the upstream Edge/CSRGraph/random_graph/free_graph
 * while parsing their header; undo the macros so this TU keeps using this
 * project's own symbols. DmCSRGraph and ssp_duan (from the port header)
 * stay visible for the DMMSY call below. */
#undef Edge
#undef CSRGraph
#undef random_graph
#undef free_graph

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

#define MAXN (1u << 22)

typedef struct {
    double *v;
    int n, cap;
} Vec;

static void vec_push(Vec *a, double x) {
    if (a->n == a->cap) { a->cap = a->cap ? a->cap * 2 : 16; a->v = realloc(a->v, (size_t)a->cap * sizeof(double)); }
    a->v[a->n++] = x;
}
static int dbl_cmp(const void *a, const void *b) {
    double x = *(const double *)a, y = *(const double *)b;
    return x < y ? -1 : x > y;
}
static double vec_min(Vec *a) {
    if (a->n == 0) return 0.0;
    double m = a->v[0]; for (int i = 1; i < a->n; i++) if (a->v[i] < m) m = a->v[i]; return m;
}
static double vec_median(Vec *a) {
    if (a->n == 0) return 0.0;
    double *t = malloc((size_t)a->n * sizeof(double));
    memcpy(t, a->v, (size_t)a->n * sizeof(double));
    qsort(t, (size_t)a->n, sizeof(double), dbl_cmp);
    double m = t[a->n / 2];
    free(t);
    return m;
}

static weight_t *g_dref, *g_dchd, *g_ddm;
static node_t *g_p, *g_pp;
static int g_bad = 0;

static void check(const char *tag, const CSRGraph *g, const weight_t *d) {
    if (!graph_equal_dist(g_dref, d, g->n)) {
        node_t v = 0;
        while (graph_equal_dist(g_dref + v, d + v, 1)) v++;
        printf("  !! WRONG %s: first mismatch v=%u got=%.17g want=%.17g\n",
               tag, v, d[v], g_dref[v]);
        g_bad++;
    }
}

int main(int argc, char **argv) {
    int max_exp = argc > 1 ? atoi(argv[1]) : 20;   /* largest n = 2^max_exp */
    int reps    = argc > 2 ? atoi(argv[2]) : 5;
    if (max_exp < 16) max_exp = 16;
    if (max_exp > 22) {                           /* dist/pred buffers are MAXN */
        printf("max_exp clamped to 22 (MAXN = 2^22)\n");
        max_exp = 22;
    }
    /* min/median need at least one timed interleaved rep besides the
     * verification pass (which only times Dijkstra) */
    if (reps < 2) {
        printf("reps clamped to 2 (min/median need one timed rep)\n");
        reps = 2;
    }

    /* optional paper-parameter experiment: CHD_T overrides t (0 = paper) */
    const char *ts = getenv("CHD_T");
    if (ts && atoi(ts) > 0) {
        chd_set_t_override((uint32_t)atoi(ts));
        printf("C-HD parameter override: t=%d (paper default would be recomputed)\n", atoi(ts));
    }

    char cpu[256]; cpu_model(cpu, sizeof(cpu));
    printf("CPU: %s\n", cpu);
    printf("compiler: MSVC, /O2 /Ob3, no /arch tuning (portable baseline)\n");
    printf("methods: C-HD (chd_sssp, incl. preprocessing) | "
           "DMMSY (ssp_duan, Duan et al. STOC'25) | Dijkstra (4-ary heap)\n");
    printf("timing : %d interleaved round-robin reps per cell; min | median\n\n", reps);

    g_dref = malloc(MAXN * sizeof(weight_t));
    g_dchd = malloc(MAXN * sizeof(weight_t));
    g_ddm  = malloc(MAXN * sizeof(weight_t));
    g_p    = malloc(MAXN * sizeof(node_t));
    g_pp   = malloc(MAXN * sizeof(node_t));

    FILE *csv = fopen("bench_results.csv", "w");
    fprintf(csv, "n,m_ratio,algo,time_min_s,time_median_s\n");

    printf("%-10s %-7s | %-14s | %-14s | %-14s\n",
           "n", "m/n", "C-HD", "DMMSY", "Dijkstra");
    printf("--------------------------------------------------------------------------\n");

    const int ratios[] = {4, 8};
    for (int e = 16; e <= max_exp; e++) {
        node_t n = (node_t)1 << e;
        for (unsigned ri = 0; ri < sizeof(ratios)/sizeof(ratios[0]); ri++) {
            node_t m = n * (node_t)ratios[ri];
            uint64_t seed = 0xB5EDu * (uint64_t)e * 131u + (uint64_t)ratios[ri];
            CSRGraph g = random_graph(n, m, 100.0, seed);
            node_t src = (node_t)(seed % n);

            /* reference + verification pass */
            double t0 = now_seconds();
            dijkstra_ref(&g, src, g_dref, NULL);
            double tref1 = now_seconds() - t0;

            chd_sssp(&g, src, g_dchd, g_p);
            check("C-HD", &g, g_dchd);
            fprintf(stderr, "  [stats] n=%u m/n=%d calls=%llu base=%llu fp=%llu pulls=%llu inserts=%llu merged=%llu deleted=%llu\n",
                    n, ratios[ri],
                    (unsigned long long)chd_last_stat(0), (unsigned long long)chd_last_stat(1),
                    (unsigned long long)chd_last_stat(2), (unsigned long long)chd_last_stat(6),
                    (unsigned long long)chd_last_stat(5), (unsigned long long)chd_last_stat(7),
                    (unsigned long long)chd_last_stat(4));
            ssp_duan((DmCSRGraph *)&g, src, g_ddm, g_pp); /* layout-identical, read-only */
            check("DMMSY", &g, g_ddm);

            Vec tchd = {0}, tdm = {0}, tdij = {0};
            vec_push(&tdij, tref1);   /* reference pass doubles as rep 1 */
            for (int r = 0; r < reps - 1; r++) {
                double a = now_seconds();
                chd_sssp(&g, src, g_dchd, g_p);
                double b = now_seconds();
                ssp_duan((DmCSRGraph *)&g, src, g_ddm, g_pp);
                double c = now_seconds();
                dijkstra_ref(&g, src, g_dref, NULL);
                double d = now_seconds();
                vec_push(&tchd, b - a);
                vec_push(&tdm, c - b);
                vec_push(&tdij, d - c);
            }
            double chd_min = vec_min(&tchd), chd_med = vec_median(&tchd);
            double dm_min = vec_min(&tdm), dm_med = vec_median(&tdm);
            double dj_min = vec_min(&tdij), dj_med = vec_median(&tdij);

            printf("%-10u %-7d | %7.1f %7.1f | %7.1f %7.1f | %7.1f %7.1f   (ms, min/med)\n",
                   n, ratios[ri],
                   chd_min * 1e3, chd_med * 1e3,
                   dm_min * 1e3, dm_med * 1e3,
                   dj_min * 1e3, dj_med * 1e3);
            fprintf(csv, "%u,%d,chd,%g,%g\n", n, ratios[ri], chd_min, chd_med);
            fprintf(csv, "%u,%d,dmmsy,%g,%g\n", n, ratios[ri], dm_min, dm_med);
            fprintf(csv, "%u,%d,dijkstra,%g,%g\n", n, ratios[ri], dj_min, dj_med);
            fflush(csv);

            free(tchd.v); free(tdm.v); free(tdij.v);
            free_graph(&g);
        }
        printf("\n");
    }
    fclose(csv);

    printf("CSV written: bench_results.csv\n");
    printf("verification: %s\n", g_bad ? "FAILURES PRESENT (see !! lines)" : "all algos match Dijkstra");
    free(g_dref); free(g_dchd); free(g_ddm); free(g_p); free(g_pp);
    return g_bad ? 1 : 0;
}
