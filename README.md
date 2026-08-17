# #Knapsack: A Faster FPTAS

Companion repository for the paper **"A Faster FPTAS for #Knapsack"**
(Pawel Gawrychowski, Liran Markin, Oren Weimann, **ICALP 2018**,
[DOI: 10.4230/LIPIcs.ICALP.2018.64](https://doi.org/10.4230/LIPIcs.ICALP.2018.64)).

#Knapsack asks: given integer weights w1, ..., wn and a capacity C, how many
subsets have total weight at most C? The problem is #P-hard; the paper gives
the fastest known deterministic (1+eps)-approximation scheme, running in
O(n^2.5 eps^-1.5 log(n eps^-1) log(n eps)) time.

## Contents

- [`faster-fptas-knapsack.pdf`](faster-fptas-knapsack.pdf) - the paper.
- [`lean/`](lean/) - **formal verification** in Lean 4: the algorithm as an
  executable function together with a machine-checked, sorry-free proof of
  Theorem 1's correctness guarantee
  (`exact <= answer <= (1+eps) * exact`). See [`lean/README.md`](lean/README.md).
- [`python/`](python/) - a short, readable **Python reference implementation**
  of the same algorithm, with differential tests against exact counting.
  See [`python/README.md`](python/README.md).

## Quick start

```sh
# Python (no dependencies)
python3 python/sharp_knapsack.py 1/10 15 3 1 4 1 5 9 2 6

# Lean (requires elan; downloads the mathlib cache on first build)
cd lean && lake exe cache get && lake build && lake exe sharpknapsack 1/10 15 3 1 4 1 5 9 2 6
```

Both print the approximate subset count (128 for this instance - here the
approximation happens to be exact).
