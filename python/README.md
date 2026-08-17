# Python reference implementation

A short, readable implementation of the paper's divide-and-conquer FPTAS
(~150 lines, no dependencies, exact int/Fraction arithmetic). It mirrors the
formally verified Lean version in [`../lean`](../lean) - same structure, same
constants - so it can serve as a guide when reading either the paper or the
proofs.

## Run

```sh
python3 sharp_knapsack.py 1/10 15 3 1 4 1 5 9 2 6
```

Arguments: eps (rational in (0,1]), capacity, then the weights. For modest
instances it also prints the exact count (dynamic programming) for comparison.

## Test

```sh
python3 tests.py
```

Checks `exact <= approx <= (1+eps) * exact` for both algorithms (Section 3
insertion and Section 4 divide-and-conquer) on fixed and randomized instances
over every capacity, and cross-validates the DP reference against literal
subset enumeration.

Note: unlike the Lean version, nothing here is proven - the guarantee is
inherited from the paper (and from the Lean proof of the same algorithm).
