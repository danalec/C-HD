# DMMSY reference implementation (vendored)

Sources from [DMMSY-SSSP](https://github.com/danalec/DMMSY-SSSP)
(Duan, Mao, Mao, Shu, Yin — *Breaking the Sorting Barrier for Directed
Single-Source Shortest Paths*, STOC 2025), adapted only with MSVC / ISO-C
portability shims (`__thread`, etc.).  Used read-only by the benchmark
driver (`src/benchmark.c`) as the honest comparison baseline.

Dual-licensed upstream: see `LICENSE-MIT` and `LICENSE-APACHE` in this
directory.
