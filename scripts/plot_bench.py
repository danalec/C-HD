# -*- coding: utf-8 -*-
"""Generate the benchmark figures from results/bench_results_final.csv."""
import csv
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

rows = list(csv.DictReader(open("results/bench_results_final.csv")))
data = {}   # (n, ratio, algo) -> (min_s, med_s)
for r in rows:
    data[(int(r["n"]), int(r["m_ratio"]), r["algo"])] = (
        float(r["time_min_s"]), float(r["time_median_s"]))

ns = sorted({k[0] for k in data})
ratios = sorted({k[1] for k in data})
algos = ["chd", "dmmsy", "dijkstra"]
names = {"chd": "C-HD (this work)", "dmmsy": "DMMSY (Duan et al. STOC'25)",
         "dijkstra": "Dijkstra (4-ary heap)"}
styles = {"chd": ("o-", "#d62728"), "dmmsy": ("s--", "#1f77b4"),
          "dijkstra": ("^:", "#7f7f7f")}

fig, axes = plt.subplots(1, 2, figsize=(13, 5.2))
for ax, ratio in zip(axes, ratios):
    for algo in algos:
        xs = [n for n in ns if (n, ratio, algo) in data]
        ys = [data[(n, ratio, algo)][0] * 1e3 for n in xs]
        mk, c = styles[algo]
        ax.plot(xs, ys, mk, color=c, label=names[algo], linewidth=2, markersize=6)
    ax.set_xscale("log", base=2)
    ax.set_yscale("log")
    ax.set_xlabel("n (vertices)")
    ax.set_title(f"random digraphs, m/n = {ratio}  (min of 5 runs)")
    ax.grid(True, which="both", alpha=0.3)
    ax.set_ylabel("time (ms)")
axes[0].legend()
fig.suptitle("SSSP on sparse random digraphs — AMD Ryzen 9 7950X3D, MSVC /O2 (portable, no cache tuning)")
fig.tight_layout(rect=[0, 0, 1, 0.94])
fig.savefig("results/fig_benchmark.png", dpi=150)
plt.close(fig)

# speedup figure: how many times slower C-HD is vs DMMSY and vs Dijkstra
fig, ax = plt.subplots(figsize=(8, 5))
width = 0.35
x = range(len(ns))
for ratio, off in zip(ratios, (-width / 2, width / 2)):
    ys_dm = [data[(n, ratio, "dmmsy")][0] and
             data[(n, ratio, "chd")][0] / data[(n, ratio, "dmmsy")][0] for n in ns]
    ys_dj = [data[(n, ratio, "chd")][0] / data[(n, ratio, "dijkstra")][0] for n in ns]
    ax.bar([i + off for i in x], ys_dm, width,
           label=f"vs DMMSY (m/n={ratio})", color="#1f77b4" if ratio == 4 else "#2ca02c")
    ax.bar([i + off for i in x], ys_dj, width, bottom=ys_dm,
           label=f"vs Dijkstra (m/n={ratio})", color="#aec7e8" if ratio == 4 else "#c7e9c0")
ax.axhline(1.0, color="k", linewidth=0.8)
ax.set_xticks(list(x))
ax.set_xticklabels([f"2^{i.bit_length()-1}" for i in ns])
ax.set_xlabel("n (vertices)")
ax.set_ylabel("C-HD time / baseline time (min of 5)")
ax.set_title("C-HD relative cost — below 1 means C-HD is faster")
ax.legend()
ax.grid(True, axis="y", alpha=0.3)
fig.tight_layout()
fig.savefig("results/fig_speedup.png", dpi=150)
plt.close(fig)
print("wrote results/fig_benchmark.png and results/fig_speedup.png")
