"""Differential tests: both algorithms vs the exact count, on every capacity.

Run with: python3 tests.py  (exits non-zero on any failure, no dependencies)
"""

import random
from fractions import Fraction
from itertools import combinations

from sharp_knapsack import approx_count, dc, exact_count, halman, query_le, sparsify

failures = 0


def check(name: str, cond: bool) -> None:
    global failures
    if not cond:
        failures += 1
        print(f"FAIL: {name}")


def enum_count(weights: list[int], capacity: int) -> int:
    """Independent second reference: literal subset enumeration."""
    return sum(
        1
        for k in range(len(weights) + 1)
        for c in combinations(weights, k)
        if sum(c) <= capacity
    )


def check_instance(weights: list[int], eps: Fraction, up_to: int) -> None:
    kh = halman(weights, eps)
    kd = dc(weights, eps)
    for cap in range(up_to):
        exact = exact_count(weights, cap)
        for label, approx in (("halman", query_le(kh, cap)),
                              ("dc", query_le(kd, cap))):
            check(
                f"{label} {weights} eps={eps} C={cap}: {exact} <= {approx} <= (1+eps)*exact",
                exact <= approx and approx <= (1 + eps) * exact,
            )


# The DP reference agrees with literal enumeration.
for ws in ([], [0, 0, 3], [3, 1, 4, 1, 5], [7] * 6, [10, 10, 1]):
    for cap in range(0, 25, 3):
        check(f"dp vs enum {ws} C={cap}", exact_count(ws, cap) == enum_count(ws, cap))

# Fixed instances, several eps values.
for eps in (Fraction(1), Fraction(1, 2), Fraction(1, 10), Fraction(1, 100)):
    check_instance([3, 1, 4, 1, 5, 9, 2, 6], eps, 40)
    check_instance([5] * 12, eps, 65)
    check_instance([100, 1, 50, 2, 25, 4, 12, 8], eps, 210)
    check_instance([], eps, 5)
    check_instance([0, 0, 7], eps, 15)

# Randomized instances (fixed seed).
rng = random.Random(2018)
for _ in range(15):
    n = rng.randint(1, 18)
    ws = [rng.randint(0, 30) for _ in range(n)]
    eps = Fraction(1, rng.randint(1, 40))
    check_instance(ws, eps, sum(ws) + 2)

# approx_count == query of dc (the CLI path).
check("approx_count path",
      approx_count([3, 1, 4], 5, Fraction(1, 2))
      == query_le(dc([3, 1, 4], Fraction(1, 2)), 5))

# Sparsify compresses and, at delta = 0, is exact on prefix sums.
pts = [(i, 1) for i in range(100)]
check("sparsify compresses", len(sparsify(Fraction(1, 2), pts)) <= 15)
check("sparsify delta=0 exact",
      all(query_le(sparsify(Fraction(0), pts), x) == query_le(pts, x)
          for x in range(110)))

if failures:
    print(f"{failures} failure(s)")
    raise SystemExit(1)
print("all tests passed")
