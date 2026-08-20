# Probe: in-band crossing complexity of sum-approximation merges.
# X = #pairs (k,l) whose position-sum T crosses while the output
# cumulative at T is <= r_{k+l+w} (w = accuracy band O~(log(s)/delta)).
# Regime of interest: s >> w. Question: X ~ s*poly(1/delta) or s^2?
import math
import numpy as np

def make_instance(kind, s, rng):
    # directly produce breakpoint positions x_0<=...<=x_{s-1}
    # (block k has implicit mass ~ delta*(1+delta)^k)
    if kind == "uniform-log":       # positions equally spaced in log-scale
        return np.cumsum(np.full(s, 1000.0))
    if kind == "doubling":          # positions double: x_k = 2^k-ish scaled
        return np.logspace(0, s / 50.0, s, base=2.0)
    if kind == "random-gaps":
        return np.cumsum(rng.pareto(1.2, s) + 1.0)
    if kind == "atoms":             # long flat runs (atoms) at spread positions
        base = np.repeat(np.arange(1, s // 50 + 2) * 1e7, 50)[:s]
        return base + np.arange(s) * 1e-3
    if kind == "slow-then-jump":    # crafted: slow growth then jumps
        x = np.ones(s)
        x[:: 7] = 1e6
        return np.cumsum(x)

def inband_count(xF, xG, delta, w):
    s = len(xF)
    lg = math.log1p(delta)
    K, L = np.meshgrid(np.arange(s), np.arange(s), indexing="ij")
    T = (xF[:, None] + xG[None, :]).ravel()
    D = (K + L).ravel()
    order = np.argsort(T, kind="stable")
    Ts, Ds = T[order], D[order]
    logmass = Ds * lg + 2 * math.log(delta)
    # exact cumulative in log space
    cum = np.logaddexp.accumulate(logmass)
    m = cum / lg
    inband = m <= Ds + w
    return int(inband.sum()), s * s

rng = np.random.default_rng(5)
delta = 0.1
print(f"{'kind':>14} {'s':>6} {'w':>5} {'pairs':>10} {'X':>10} {'X/s':>8} {'X/pairs':>8}")
rows = {}
for kind in ["uniform-log", "doubling", "random-gaps", "atoms", "slow-then-jump"]:
    rows[kind] = []
    for s in [500, 1000, 2000]:
        xF = make_instance(kind, s, rng)
        xG = make_instance(kind, s, rng)
        w = math.log(s / delta**2) / math.log1p(delta)
        X, pairs = inband_count(np.sort(xF), np.sort(xG), delta, w)
        rows[kind].append((s, X))
        print(f"{kind:>14} {s:>6} {w:>5.0f} {pairs:>10} {X:>10} {X/s:>8.1f} {X/pairs:>8.4f}")
for kind, r in rows.items():
    g2 = r[2][1] / r[1][1]
    print(f"{kind:>14}: growth {g2:.2f}  (2.0 = linear, 4.0 = quadratic)")
# B3 assertions: a quadratic witness family exists (arithmetic positions,
# geometric values - every pair crosses in-band), AND genuinely wild
# families are subquadratic (the dichotomy's two poles).
assert rows["uniform-log"][2][1] == 2000 * 2000, "quadratic witness must saturate"
assert abs(rows["uniform-log"][2][1] / rows["uniform-log"][1][1] - 4.0) < 0.1, \
    "witness family must grow quadratically"
assert rows["doubling"][2][1] < 0.3 * 2000 * 2000, "wild family must be subquadratic"
assert rows["doubling"][2][1] / rows["doubling"][1][1] < 2.6, \
    "wild family growth must be near-linear"
print("all in-band crossing assertions passed (B3: quadratic witness + subquadratic wild)")
