#include "dmmsy.h"
#include <math.h>
#include <stdlib.h>
#include <string.h>

typedef struct {
  weight_t *d;
  node_t *pr;
  HeapNode *h_nodes; // n + 1
  node_t *h_pos;     // n
  node_t *dirty_h;   // n
  node_t dh_cnt;
  node_t *dirty_d; // n
  node_t ds_cnt;
  node_t **piv_bufs; // Number of max depth levels
  node_t max_depth;
  node_t n;
} WorkSpace;

static __thread WorkSpace *ws_opt = NULL;

static WorkSpace *get_workspace(node_t n, Params p) {
  if (ws_opt == NULL) {
    ws_opt = (WorkSpace *)malloc(sizeof(WorkSpace));
    ws_opt->n = n;
    ws_opt->d = (weight_t *)malloc(sizeof(weight_t) * n);
    ws_opt->pr = (node_t *)malloc(sizeof(node_t) * n);
    ws_opt->h_nodes = (HeapNode *)malloc(sizeof(HeapNode) * (n + 1));
    ws_opt->h_pos = (node_t *)malloc(sizeof(node_t) * n);
    ws_opt->dirty_h = (node_t *)malloc(sizeof(node_t) * n);
    ws_opt->dh_cnt = 0;
    ws_opt->dirty_d = (node_t *)malloc(sizeof(node_t) * n);
    ws_opt->ds_cnt = 0;

    ws_opt->max_depth = p.t + 2;
    ws_opt->piv_bufs = (node_t **)malloc(sizeof(node_t *) * ws_opt->max_depth);
    node_t buf_size = p.k > 4 ? p.k : 4;

    for (node_t i = 0; i < ws_opt->max_depth; i++) {
      ws_opt->piv_bufs[i] = (node_t *)malloc(sizeof(node_t) * buf_size);
    }

    // Final init
    for (node_t i = 0; i < n; i++)
      ws_opt->h_pos[i] = 0;
    for (node_t i = 0; i < n; i++)
      ws_opt->d[i] = WEIGHT_MAX;

  } else if (ws_opt->n != n) {

    for (node_t i = 0; i < ws_opt->max_depth; i++)
      free(ws_opt->piv_bufs[i]);
    free(ws_opt->piv_bufs);
    free(ws_opt->d);
    free(ws_opt->pr);
    free(ws_opt->h_nodes);
    free(ws_opt->h_pos);
    free(ws_opt->dirty_h);
    free(ws_opt->dirty_d);
    free(ws_opt);
    ws_opt = NULL;
    return get_workspace(n, p);
  }
  return ws_opt;
}

static inline void bmsp_rec(DmCSRGraph *g, node_t *src_buf, node_t off_src,
                            node_t len_src, weight_t B, node_t dp,
                            WorkSpace *ws, Params p) {
  if (dp >= p.t || len_src <= p.k) {
    if (ws->dh_cnt > 0) {
      for (node_t i = 0; i < ws->dh_cnt; i++)
        ws->h_pos[ws->dirty_h[i]] = 0;
      ws->dh_cnt = 0;
    }

    Fast4AryHeap h;
    h.nodes = ws->h_nodes;
    h.pos = ws->h_pos;
    h.dirty = ws->dirty_h;
    h.max_size = g->n;

    node_t sz = 0, dcnt = 0;

    for (node_t i = 0; i < len_src; i++) {
      node_t s = src_buf[off_src + i];
      push_dec(&h, &sz, &dcnt, s, ws->d[s]);
    }
    ws->dh_cnt = dcnt;

    while (sz > 0) {
      weight_t du;
      node_t u;
      pop_min(&h, &sz, &du, &u);

      if (du > ws->d[u])
        continue;

      node_t u_off = g->offset[u];
      node_t u_end = g->offset[u + 1];

      for (node_t i = u_off; i < u_end; i++) {
        node_t v = g->edges[i].v;
        weight_t w = g->edges[i].w;
        weight_t nd = du + w;

        if (nd < ws->d[v]) {
          if (ws->d[v] == WEIGHT_MAX) {
            ws->dirty_d[ws->ds_cnt++] = v;
          }
          ws->d[v] = nd;
          ws->pr[v] = u;
          push_dec(&h, &sz, &ws->dh_cnt, v, nd);
        }
      }
    }
    return;
  }

  node_t np = (len_src < p.k) ? len_src : p.k;
  node_t *pivots = ws->piv_bufs[dp + 2];
  node_t step = len_src / np;
  if (step == 0)
    step = 1;

  node_t curr_np = 0;
  node_t bound = len_src < (step * p.k) ? len_src : (step * p.k);

  for (node_t i = 0; i < bound; i += step) {
    pivots[curr_np++] = src_buf[off_src + i];
  }

  bmsp_rec(g, pivots, 0, curr_np, B * 0.5, dp + 1, ws, p);

  // Main loop processing
  if (ws->dh_cnt > 0) {
    for (node_t i = 0; i < ws->dh_cnt; i++)
      ws->h_pos[ws->dirty_h[i]] = 0;
    ws->dh_cnt = 0;
  }

  Fast4AryHeap h;
  h.nodes = ws->h_nodes;
  h.pos = ws->h_pos;
  h.dirty = ws->dirty_h;
  h.max_size = g->n;

  node_t sz = 0, dcnt = 0;
  bool has_work = false;

  for (node_t i = 0; i < len_src; i++) {
    node_t s = src_buf[off_src + i];
    weight_t dv = ws->d[s];
    if (dv < B) {
      push_dec(&h, &sz, &dcnt, s, dv);
      has_work = true;
    }
  }
  ws->dh_cnt = dcnt;

  if (!has_work)
    return;

  while (sz > 0) {
    weight_t du;
    node_t u;
    pop_min(&h, &sz, &du, &u);

    if (du > ws->d[u])
      continue;

    node_t u_off = g->offset[u];
    node_t u_end = g->offset[u + 1];

    for (node_t i = u_off; i < u_end; i++) {
      node_t v = g->edges[i].v;
      weight_t w = g->edges[i].w;
      weight_t nd = du + w;

      if (nd < ws->d[v]) {
        if (ws->d[v] == WEIGHT_MAX) {
          ws->dirty_d[ws->ds_cnt++] = v;
        }
        ws->d[v] = nd;
        ws->pr[v] = u;
        if (nd < B) {
          push_dec(&h, &sz, &ws->dh_cnt, v, nd);
        }
      }
    }
  }
}

void ssp_duan(DmCSRGraph *g, node_t src, weight_t *d_out, node_t *pr_out) {
  if (g->n == 0)
    return;

  Params p = get_params(g->n);
  WorkSpace *ws = get_workspace(g->n, p);

  if (ws->ds_cnt > (g->n >> 2)) {
    for (node_t i = 0; i < g->n; i++)
      ws->d[i] = WEIGHT_MAX;
    for (node_t i = 0; i < g->n; i++)
      ws->pr[i] = 0;
    for (node_t i = 0; i < g->n; i++)
      ws->pr[i] = NODE_MAX;
  } else {
    for (node_t i = 0; i < ws->ds_cnt; i++) {
      node_t idx = ws->dirty_d[i];
      ws->d[idx] = WEIGHT_MAX;
      ws->pr[idx] = NODE_MAX;
    }
  }

  ws->ds_cnt = 1;
  ws->d[src] = 0.0;
  ws->dirty_d[0] = src;
  ws->dh_cnt = 0;

  double log2_n1 = log2((double)(g->n + 1));
  weight_t B = g->mean_weight * log2_n1 * 4.0;

  ws->piv_bufs[1][0] = src;
  bmsp_rec(g, ws->piv_bufs[1], 0, 1, B, 0, ws, p);

  if (d_out)
    memcpy(d_out, ws->d, sizeof(weight_t) * g->n);
  if (pr_out)
    memcpy(pr_out, ws->pr, sizeof(node_t) * g->n);
}
