# Probe: order-exact piecewise-linear fit covers of breakpoint sequences.
# Greedy: extend the segment while a linear model (slope = running mean
# gap) keeps every residual below a third of the local gap - the
# condition under which model crossings preserve true crossing order
# up to O(1). rho = #segments. If rho stays near-sqrt(s) or smaller on
# every family, merge cost rho^2*polylog is subquadratic and the
# record-reduction lemma is plausible.
import math
import numpy as np

def order_exact_fit_cover(x):
    s = len(x)
    if s <= 2: return 1
    rho = 0
    i = 0
    while i < s:
        rho += 1
        j = i + 1
        if j >= s: break
        while j < s:
            seg = x[i:j+1]
            L = j - i
            slope = (x[j] - x[i]) / max(L, 1)
            model = x[i] + slope * np.arange(L + 1)
            resid = np.abs(seg - model)
            gaps = np.diff(seg)
            local = np.minimum(np.concatenate([gaps, [np.inf]]),
                               np.concatenate([[np.inf], gaps]))
            tol = np.maximum(local / 3.0, 1e-12)
            if np.all(resid <= tol) or np.all(gaps < 1e-9):
                j += 1
            else:
                break
        i = j
    return rho

def make(kind, s, rng):
    if kind == "arith":       return np.cumsum(np.full(s, 1000.0))
    if kind == "doubling":    return np.logspace(0, s / 50.0, s, base=2.0)
    if kind == "random-gaps": return np.cumsum(rng.pareto(1.2, s) + 1.0)
    if kind == "uniform-rand":return np.sort(rng.uniform(0, 1e9, s))
    if kind == "atoms":
        return np.repeat(np.cumsum(rng.uniform(1e5, 1e6, max(1, s // 50))), 50)[:s].astype(float)
    if kind == "noisy-arith":
        return np.arange(s) * 1000.0 + rng.uniform(-400, 400, s)
    if kind == "multi-scale":
        # arithmetic at top scale, wild at fine scale, nested
        base = np.arange(s) * 1e6
        mid = (np.arange(s) % 97) * 1e3
        fine = rng.pareto(1.5, s) * 10
        return np.sort(base + mid + fine)
    if kind == "convex":
        return np.cumsum(np.arange(1, s + 1, dtype=float))

rng = np.random.default_rng(21)
print(f"{'kind':>13} {'s':>6} {'rho':>6} {'rho^2/s^2':>10} {'rho/sqrt(s)':>11}")
grow = {}
for kind in ["arith", "doubling", "random-gaps", "uniform-rand", "atoms",
             "noisy-arith", "multi-scale", "convex"]:
    rhos = []
    for s in [1000, 4000, 16000]:
        x = np.sort(make(kind, s, rng))
        rho = order_exact_fit_cover(x)
        rhos.append(rho)
        print(f"{kind:>13} {s:>6} {rho:>6} {rho*rho/(s*s):>10.4f} {rho/math.sqrt(s):>11.2f}")
    grow[kind] = (rhos[2] / max(rhos[1], 1), rhos)
print()
for kind, (g, rhos) in grow.items():
    print(f"{kind:>13}: rho growth x4-s = {g:.2f}  (2.0 = sqrt-like, 4.0 = linear-in-s)")

# HONEST findings: single-scale ORDER-EXACT fits compress only
# structured families; wild/noisy families give rho ~ s (linear growth).
assert grow["arith"][1][2] == 1 and grow["multi-scale"][1][2] == 1
assert grow["uniform-rand"][0] > 3.0, "documenting: exact fits fail on noise"
print("fit-cover probe: exact fits insufficient alone (documented)")
