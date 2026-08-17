"""Reference implementation of "A Faster FPTAS for #Knapsack"
(Gawrychowski, Markin, Weimann, ICALP 2018).

Counts, approximately, the subsets of a list of non-negative integer weights
whose total weight is at most a capacity C, within a factor 1+eps.

The structure mirrors the paper (and the formally verified Lean version in
../lean, which uses the same constants):

- a function f : N -> N is represented sparsely as a sorted list of
  (position, value) pairs with positive values (paper Definition 7);
- `sparsify` compresses a representation while changing prefix sums by at
  most a factor 1+delta (paper Algorithm 1 / Lemma 8);
- `halman` inserts items one at a time (paper Section 3);
- `dc` recurses on the two halves of the item list and merges with a
  convolution (paper Section 4, the main algorithm).

All arithmetic is exact (int / Fraction).
"""

from fractions import Fraction
from math import floor, isqrt

SparseFun = list[tuple[int, int]]  # sorted (position, value), values > 0


def query_le(points: SparseFun, c: int) -> int:
    """Prefix sum of the represented function: f^<=(c)."""
    return sum(v for x, v in points if x <= c)


def shift(points: SparseFun, w: int) -> SparseFun:
    """The shift f|_w: move every point right by w."""
    return [(x + w, v) for x, v in points]


def add(a: SparseFun, b: SparseFun) -> SparseFun:
    """Pointwise sum f + g."""
    out: dict[int, int] = {}
    for x, v in a + b:
        out[x] = out.get(x, 0) + v
    return sorted(out.items())


def conv(a: SparseFun, b: SparseFun) -> SparseFun:
    """Convolution (f * g)(x) = sum_{y+z=x} f(y)g(z)."""
    out: dict[int, int] = {}
    for x1, v1 in a:
        for x2, v2 in b:
            out[x1 + x2] = out.get(x1 + x2, 0) + v1 * v2
    return sorted(out.items())


def sparsify(delta: Fraction, points: SparseFun) -> SparseFun:
    """Paper Algorithm 1: keep one point per breakpoint of the threshold
    sequence r <- max(r+1, floor((1+delta) r)), moving the mass of each
    segment onto its left endpoint. The result's prefix sums are within
    [f^<=, (1+delta) f^<=] (paper Lemma 8; proven in the Lean version)."""
    out: SparseFun = []
    acc = 0  # prefix sum of everything scanned so far
    r = 1  # current threshold
    pending: tuple[int, int] | None = None  # (breakpoint position, prefix sum before it)
    for x, v in points:
        before = acc
        acc += v
        if acc < r:
            continue  # not a breakpoint: mass merges into the pending segment
        if pending is not None:
            q, base = pending
            out.append((q, before - base))
        pending = (x, before)
        while r <= acc:
            r = max(r + 1, floor((1 + delta) * r))
    if pending is not None:
        q, base = pending
        out.append((q, acc - base))
    return out


def insert_item(delta: Fraction, k: SparseFun, w: int) -> SparseFun:
    """Insert one item of weight w: k <- sparsify(k + k|_w) (paper Lemma 9)."""
    return sparsify(delta, add(k, shift(k, w)))


def halman(weights: list[int], eps: Fraction) -> SparseFun:
    """Paper Section 3: insert items one at a time with per-item
    delta = eps/(2n), giving an overall factor at most 1+eps."""
    n = len(weights)
    delta = eps / (2 * n) if n else Fraction(0)
    k: SparseFun = [(0, 1)]  # the empty set: one subset of weight 0
    for w in weights:
        k = insert_item(delta, k, w)
    return k


def delta_at(eps: Fraction, d: int) -> Fraction:
    """Sparsification parameter at recursion depth d."""
    return eps / 20 * Fraction(2, 5) ** d


def _dc_go(eps: Fraction, threshold: int, weights: list[int], d: int) -> SparseFun:
    if len(weights) <= max(1, threshold):
        return halman(weights, delta_at(eps, d))
    k = len(weights) // 2
    return sparsify(
        delta_at(eps, d),
        conv(_dc_go(eps, threshold, weights[:k], d + 1),
             _dc_go(eps, threshold, weights[k:], d + 1)),
    )


def dc(weights: list[int], eps: Fraction) -> SparseFun:
    """Paper Section 4: split in the middle, recurse, merge with a
    convolution (paper Lemma 10), sparsify with a depth-decaying delta.
    Sets of size up to ~sqrt(n) are handled by `halman`."""
    return _dc_go(eps, isqrt(len(weights)), weights, 0)


def approx_count(weights: list[int], capacity: int, eps: Fraction) -> int:
    """The answer to the #Knapsack instance: an approximation A with

        exact <= A <= (1+eps) * exact

    for 0 < eps <= 1 (the paper's Theorem 1, machine-checked in ../lean)."""
    return query_le(dc(weights, eps), capacity)


def exact_count(weights: list[int], capacity: int) -> int:
    """Exact count by standard O(n*C) dynamic programming, for reference."""
    dp = [0] * (capacity + 1)
    dp[0] = 1
    for w in weights:
        if w == 0:
            dp = [2 * v for v in dp]
        elif w <= capacity:
            for c in range(capacity, w - 1, -1):
                dp[c] += dp[c - w]
    return sum(dp)


def main() -> int:
    import sys

    args = sys.argv[1:]
    if len(args) < 2:
        print("usage: python3 sharp_knapsack.py <eps> <capacity> <w1> <w2> ...",
              file=sys.stderr)
        print("example: python3 sharp_knapsack.py 1/10 15 3 1 4 1 5 9 2 6",
              file=sys.stderr)
        return 1
    try:
        eps = Fraction(args[0])
    except (ValueError, ZeroDivisionError):
        print(f"error: cannot parse eps from '{args[0]}' (expected e.g. 1/10)",
              file=sys.stderr)
        return 1
    if not 0 < eps <= 1:
        print(f"error: eps must satisfy 0 < eps <= 1, got {eps}", file=sys.stderr)
        return 1
    try:
        capacity = int(args[1])
        weights = [int(a) for a in args[2:]]
        if capacity < 0 or any(w < 0 for w in weights):
            raise ValueError
    except ValueError:
        print("error: capacity and weights must be non-negative integers",
              file=sys.stderr)
        return 1
    answer = approx_count(weights, capacity, eps)
    print(f"items: {len(weights)}, capacity: {capacity}, eps = {eps}")
    print(f"approximate #subsets with weight <= {capacity}: {answer}")
    if len(weights) * (capacity + 1) <= 10**7:
        print(f"exact (dynamic programming, for comparison): "
              f"{exact_count(weights, capacity)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
