#ifndef DMMSY_COMMON_H
#define DMMSY_COMMON_H

/* MSVC / ISO-C portability shims for the original DMMSY-SSSP sources
 * (the upstream code targets C99 + GNU/Clang extensions). */
#ifdef _MSC_VER
#define __thread __declspec(thread)
#endif

#include <math.h>
#include <stdint.h>
#include <stdbool.h>

typedef uint32_t node_t;
typedef double weight_t;

/* Infinity equivalent for double */
#ifdef _MSC_VER
#define WEIGHT_MAX ((weight_t)HUGE_VAL)
#else
#define WEIGHT_MAX __builtin_inf()
#endif
#define NODE_MAX ((node_t)-1)

/* DmEdge structure */
typedef struct {
  node_t v;
  weight_t w;
} DmEdge;

/* CSR Graph structure (layout-identical to the C-HD DmCSRGraph) */
typedef struct {
  node_t n;
  node_t m;
  node_t *offset;   // size n + 1
  DmEdge *edges;      // size m
  weight_t mean_weight;
} DmCSRGraph;

/* Fast 4-Ary Heap Node */
typedef struct {
  weight_t v;
  node_t i;
} HeapNode;

/* Fast 4-Ary Heap */
typedef struct {
  HeapNode *nodes; // 1-indexed, size n + 1
  node_t *pos;     // size n
  node_t *dirty;   // size n
  node_t max_size;
} Fast4AryHeap;

/* Algorithm parameters structure */
typedef struct {
  node_t k;
  node_t t;
} Params;

/* Function prototypes */
Params get_params(node_t n);

/* Heap functions */
void init_heap(Fast4AryHeap *h, node_t n);
void free_heap(Fast4AryHeap *h);
void push_dec(Fast4AryHeap *h, node_t *sz, node_t *dcnt, node_t n, weight_t d);
void pop_min(Fast4AryHeap *h, node_t *sz, weight_t *mv, node_t *mn);

/* DMMSY entry point (Duan et al., STOC 2025) */
void ssp_duan(DmCSRGraph *g, node_t src, weight_t *d_out, node_t *pr_out);

#endif // DMMSY_COMMON_H
