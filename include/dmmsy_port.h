#ifndef DMMSY_PORT_H
#define DMMSY_PORT_H

/*
 * dmmsy_port.h — compiles the upstream DMMSY-SSSP sources VERBATIM.
 *
 * The benchmark links the original code from the ref-dmmsy git submodule
 * (github.com/danalec/DMMSY-SSSP, pinned) instead of a vendored copy.
 * Upstream targets C99 + GNU/Clang extensions and shares type/function
 * names with this project's own chd.h/common.c, so its translation units
 * are built with this header force-included (/FI include/dmmsy_port.h):
 *
 *   - MSVC shims: __thread, __builtin_inf()
 *   - symbol isolation: Edge / CSRGraph / random_graph / free_graph are
 *     renamed away before the upstream header is parsed, uniformly across
 *     its declarations and definitions, so both object sets link cleanly.
 *
 * src/benchmark.c includes this header directly for the DmCSRGraph type
 * (layout-identical to this project's CSRGraph) and the ssp_duan decl.
 */

#ifdef _MSC_VER
#define __thread __declspec(thread)
#define __builtin_inf() (HUGE_VAL)
#include <math.h>
#endif

#define Edge DmEdge
#define CSRGraph DmCSRGraph
#define random_graph dm_random_graph
#define free_graph dm_free_graph

#include "../ref-dmmsy/include/common.h"

/* not declared by the upstream header */
void ssp_duan(DmCSRGraph *g, node_t src, weight_t *d_out, node_t *pr_out);

#endif /* DMMSY_PORT_H */
