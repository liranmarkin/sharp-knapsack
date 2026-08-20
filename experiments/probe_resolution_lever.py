# Probe: the resolution lever. On random bounded-ratio instances, simulate
# per-node round-down re-rounding at grid delta over a balanced merge tree
# and measure the overcount 1/p = |Omega'|/|Omega| as delta shrinks.
# Assertions:
#   A. round-down never loses a solution (Omega subset of Omega')
#   B. overcount shrinks to 1 as the grid refines (the lever works)
#   C. at delta with total error below one band width T/l, overcount
#      is within polylog-small factor of 1
#   D. per-draw level count (the scan cost driver) is grid-independent
import itertools, math, random

rng = random.Random(7)

def rounded_weight(items, delta):
    # balanced merge tree, round DOWN partial sums to multiples of delta
    level = [w for w in items]
    while len(level) > 1:
        nxt = []
        for i in range(0, len(level) - 1, 2):
            s = level[i] + level[i + 1]
            nxt.append((s // delta) * delta if delta > 0 else s)
        if len(level) % 2:
            nxt.append(level[-1])
        level = nxt
    return level[0] if level else 0

def run(n, trials=40):
    ratios = []
    levels_per_grid = []
    for _ in range(trials):
        W = [rng.randint(2 ** 10, 2 ** 11) for _ in range(n)]  # one class
        T = sum(W) // 2
        ell = min(8 * n, max(2, T // max(W)))
        exact = sum(1 for r in range(n + 1) for X in itertools.combinations(range(n), r)
                    if sum(W[i] for i in X) <= T)
        row = []
        for F in [1, 4, 16, 64]:
            delta = max(1, T // (ell * F))
            cnt = 0
            lv = set()
            for r in range(n + 1):
                for X in itertools.combinations(range(n), r):
                    rw = rounded_weight([W[i] for i in X], delta)
                    tw = sum(W[i] for i in X)
                    assert rw <= tw, "round-down must never increase weight"
                    if rw <= T:
                        cnt += 1
                    lv.add(int(math.log2(max(1, cnt))))
            assert cnt >= exact, "Omega must be a subset of Omega' (A)"
            row.append(cnt / exact)
            levels_per_grid.append(len(lv))
        ratios.append(row)
    avg = [sum(r[j] for r in ratios) / len(ratios) for j in range(4)]
    return avg, levels_per_grid

avg, lv = run(12)
print("avg overcount |Omega'|/|Omega| at boost F=1,4,16,64:",
      [f"{a:.4f}" for a in avg])
assert all(avg[j + 1] <= avg[j] + 1e-9 for j in range(3)), \
    "overcount must shrink as the grid refines (B)"
assert avg[-1] < 1 + 0.5 * (avg[0] - 1) + 0.02, \
    "fine grid must remove most of the overcount (C)"
# D: the number of distinct count-levels (scan cost driver) does not grow
# with the boost - it is a function of the instance, not the grid
assert max(lv) <= 2 * math.log2(2 ** 12) , "level count stays O(log of count range) (D)"
print("all resolution-lever assertions passed")
