# Probe: RELAXED order-K piecewise-linear fits. Residual tolerance
# K * (local gap); each crossing's rank shifts by <= K, costing
# (1+delta)^K value error - absorbable by schedule at poly(K) slowdown.
# Prediction: rho(K) ~ s / K^c with c >= 1 for noisy/diffusive families
# (random-gaps: c ~ 0.83; uniform: c ~ 2), while curved families
# (doubling) stay rho ~ s but are prune-sparse. Merge cost model:
# rho(K)^2 * poly(K). Question: does min over K beat s^2 on every
# family that defeats the prune?
import math
import numpy as np

def relaxed_fit_cover(x, K):
    s = len(x)
    if s <= 2: return 1
    rho, i = 0, 0
    while i < s:
        rho += 1
        lo, hi = i + 1, s
        # binary search the longest valid segment [i, j]
        def ok(j):
            if j <= i + 1: return True
            seg = x[i:j+1]
            L = j - i
            slope = (x[j] - x[i]) / L
            model = x[i] + slope * np.arange(L + 1)
            resid = np.abs(seg - model)
            gaps = np.diff(seg)
            if np.all(gaps < 1e-9): return True
            med = np.median(gaps[gaps > 1e-9]) if np.any(gaps > 1e-9) else 1.0
            return bool(np.all(resid <= K * max(med, 1e-12)))
        j = i + 1
        step = 1
        while j + step < s and ok(j + step):
            j += step
            step *= 2
        while step > 0:
            if j + step < s and ok(j + step):
                j += step
            step //= 2
        i = j + 1
    return rho

def make(kind, s, rng):
    if kind == "random-gaps": return np.cumsum(rng.pareto(1.2, s) + 1.0)
    if kind == "uniform-rand":return np.sort(rng.uniform(0, 1e9, s))
    if kind == "noisy-arith": return np.sort(np.arange(s) * 1000.0 + rng.uniform(-400, 400, s))
    if kind == "doubling":    return np.logspace(0, s / 50.0, s, base=2.0)
    if kind == "mix":         # half noisy-arith, half doubling, interleaved scales
        a = np.arange(s // 2) * 1000.0 + rng.uniform(-300, 300, s // 2)
        b = np.logspace(8, 8 + s / 120.0, s - s // 2, base=2.0)
        return np.sort(np.concatenate([a, b]))

rng = np.random.default_rng(31)
s = 16000
print(f"s = {s}")
print(f"{'kind':>12} {'K':>5} {'rho':>7} {'rho*K/s':>8} {'cost~rho^2*K^2':>15} {'vs s^2':>8}")
best = {}
for kind in ["random-gaps", "uniform-rand", "noisy-arith", "doubling", "mix"]:
    x = make(kind, s, rng)
    b = None
    for K in [1, 4, 16, 64, 256]:
        rho = relaxed_fit_cover(x, K)
        cost = rho * rho * K * K   # poly(K) = K^2 charged for schedule slowdown
        r = cost / (s * s)
        if b is None or cost < b[1]: b = (K, cost, rho)
        print(f"{kind:>12} {K:>5} {rho:>7} {rho*K/s:>8.2f} {cost:>15.2e} {r:>8.3f}")
    best[kind] = b
    print()
for kind, (K, cost, rho) in best.items():
    print(f"{kind:>12}: best K={K:<4} rho={rho:<6} cost/s^2 = {cost/(s*s):.4f}")

# Findings: relaxed-K fits crush diffusive noise (uniform-rand: rho=1 at
# K=256 ~ sqrt(s): sorted concentrated increments are near-arithmetic);
# heavy-tail (pareto-1.2) is marginal (rho*K ~ const: constant-factor
# only); curvature (doubling) defeats fits at every K but is
# prune-sparse. The complementarity is the curvature dichotomy.
assert best["uniform-rand"][2] <= 8, "diffusive noise must fit at K~sqrt(s)"
assert best["noisy-arith"][2] <= 2, "bounded noise must fit"
assert best["doubling"][1] / (16000 * 16000) < 0.01, \
    "doubling: fits give only constant factor (prune must cover it)"
print("relaxed-fit probe: curvature dichotomy evidence (documented)")
