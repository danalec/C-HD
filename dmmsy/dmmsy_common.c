#include "dmmsy.h"
#include <math.h>
#include <stdlib.h>

/* Shared algorithm parameters */
Params get_params(node_t n) {
  Params p;
  double log2n = log2((double)n);
  p.k = (node_t)fmax(4.0, floor(pow(log2n, 1.0 / 3.0)));
  p.t = (node_t)fmax(2.0, floor(pow(log2n, 2.0 / 3.0)));
  return p;
}

/* 4-Ary Heap */

void init_heap(Fast4AryHeap *h, node_t n) {
  h->nodes = (HeapNode *)malloc(sizeof(HeapNode) * (n + 1));
  h->pos = (node_t *)calloc(n, sizeof(node_t)); // 0 means not in heap
  h->dirty = (node_t *)malloc(sizeof(node_t) * n);
  h->max_size = n;
}

void free_heap(Fast4AryHeap *h) {
  if (h->nodes)
    free(h->nodes);
  if (h->pos)
    free(h->pos);
  if (h->dirty)
    free(h->dirty);
}

static inline void push_up(Fast4AryHeap *h, node_t i) {
  HeapNode node = h->nodes[i];
  while (i > 1) {
    node_t par = (i - 2) / 4 + 1; // 4-ary parent
    HeapNode pnode = h->nodes[par];
    if (pnode.v <= node.v)
      break;
    h->nodes[i] = pnode;
    h->pos[pnode.i] = i;
    i = par;
  }
  h->nodes[i] = node;
  h->pos[node.i] = i;
}

void push_dec(Fast4AryHeap *h, node_t *sz, node_t *dcnt, node_t n, weight_t d) {
  node_t p = h->pos[n];
  node_t i;
  if (p == 0 || p == NODE_MAX) {
    (*sz)++;
    (*dcnt)++;
    i = *sz;
    h->dirty[*dcnt - 1] = n; // 0-indexed dirty
  } else {
    i = p;
    if (d >= h->nodes[i].v)
      return;
  }

  // Assign temporary value to be pushed up
  h->nodes[i].v = d;
  h->nodes[i].i = n;
  push_up(h, i);
}

static inline void push_down(Fast4AryHeap *h, node_t i, node_t sz) {
  HeapNode node = h->nodes[i];
  while (true) {
    node_t c1 = (i * 4) - 2;
    if (c1 > sz)
      break;

    node_t mc = c1;
    weight_t mcv = h->nodes[c1].v;
    HeapNode mc_node = h->nodes[c1];

    if (c1 + 1 <= sz && h->nodes[c1 + 1].v < mcv) {
      mc = c1 + 1;
      mc_node = h->nodes[mc];
      mcv = mc_node.v;
    }
    if (c1 + 2 <= sz && h->nodes[c1 + 2].v < mcv) {
      mc = c1 + 2;
      mc_node = h->nodes[mc];
      mcv = mc_node.v;
    }
    if (c1 + 3 <= sz && h->nodes[c1 + 3].v < mcv) {
      mc = c1 + 3;
      mc_node = h->nodes[mc];
      mcv = mc_node.v;
    }

    if (node.v <= mcv)
      break;

    h->nodes[i] = mc_node;
    h->pos[mc_node.i] = i;
    i = mc;
  }
  h->nodes[i] = node;
  h->pos[node.i] = i;
}

void pop_min(Fast4AryHeap *h, node_t *sz, weight_t *mv, node_t *mn) {
  HeapNode min_node = h->nodes[1];
  *mv = min_node.v;
  *mn = min_node.i;

  h->pos[*mn] = NODE_MAX;

  if (*sz == 1) {
    (*sz)--;
    return;
  }

  HeapNode last_node = h->nodes[*sz];
  (*sz)--;

  h->nodes[1] = last_node;
  h->pos[last_node.i] = 1;
  push_down(h, 1, *sz);
}
