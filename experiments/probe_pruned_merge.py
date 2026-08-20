# Probe: the full pruned-merge pipeline.
#   1. deterministic (1+eta)-approx MinConv of breakpoint sequences
#      (scale rounding + per-level boolean convolution - FFT, det)
#   2. band-prune: keep pairs with x_k + y_l <= (1+eta)*mtilde_{k+l+w}
#   3. ideal AP-cover simulation: pairs inside AP-block pairs are
#      charged O(1) closed-form each block pair, not per cell
# Measured: total cost = minconv_cost + X_pruned_wild + blocks.
# Question: subquadratic on EVERY family, including mixes?
import math
import numpy as np

def approx_minconv_cost_and_value(x, y, eta):
    # deterministic approx MinConv: for scales, round to eta-grid,
    # boolean convolution per level. Prototype: compute exact minconv
    # via O(s^2) reference (allowed in probe), but COST-MODEL the det
    # algorithm as s/eta * polylog. Returns (cost_model, exact m_d).
    s = len(x)
    m = np.full(2 * s - 1, np.inf)
    S = (x[:, None] + y[None, :])
    for d in range(2 * s - 1):
        ks = np.arange(max(0, d - s + 1), min(s, d + 1))
        m[d] = np.min(S[ks, d - ks])
    # suffix-min to get "min over diagonals >= e"
    msuf = np.minimum.accumulate(m[::-1])[::-1]
    cost = int(s / eta * math.log2(max(s, 2)) ** 2)
    return cost, msuf

def ap_blocks(kind, s):
    # ideal AP-cover: list of (start, end) index blocks that are APs
    if kind in ("arith", "short-runs", "two-ap-mix"): return [(0, s)]
    if kind == "ap-plus-noise": return [(0, int(s * 0.9))]
    if kind == "half-ap-half-wild": return [(0, s // 2)]
    return []  # wild: no blocks

def make(kind, s, rng):
    if kind == "arith":       return np.cumsum(np.full(s, 1000.0))
    if kind == "doubling":    return np.logspace(0, s / 50.0, s, base=2.0)
    if kind == "random-gaps": return np.cumsum(rng.pareto(1.2, s) + 1.0)
    if kind == "two-ap-mix":
        a = np.arange(s // 2) * 1000.0
        b = np.arange(s - s // 2) * math.pi * 500.0 + 3.0
        return np.sort(np.concatenate([a, b]))
    if kind == "ap-plus-noise":
        a = np.arange(int(s * 0.9)) * 1000.0
        b = np.cumsum(np.sort(rng.pareto(1.1, s - len(a))) * 1e5) + 17.0
        return np.sort(np.concatenate([a, b]))
    if kind == "half-ap-half-wild":
        a = np.arange(s // 2) * 1000.0
        b = np.logspace(10, 10 + s / 100.0, s - s // 2, base=2.0)
        return np.sort(np.concatenate([a, b]))
    if kind == "short-runs":
        g = np.tile([100.0, 7000.0], s // 2)[:s]
        return np.cumsum(g)

def pruned_cost(kind, x, y, delta, eta):
    s = len(x)
    w = math.log(s / delta ** 2) / math.log1p(delta)
    mc_cost, msuf = approx_minconv_cost_and_value(x, y, eta)
    # pairs passing the prune: sum <= (1+eta) * msuf[min(d+w+1, end)]
    K, L = np.meshgrid(np.arange(s), np.arange(s), indexing="ij")
    D = (K + L)
    thr_idx = np.minimum(D + int(w) + 1, 2 * s - 2)
    passed = (x[:, None] + y[None, :]) <= (1 + eta) * msuf[thr_idx]
    # ideal AP-block handling: block-pair cells charged as 1 per block pair
    blocks = ap_blocks(kind, s)
    inblock = np.zeros((s, s), dtype=bool)
    for (a1, a2) in blocks:
        for (b1, b2) in blocks:
            inblock[a1:a2, b1:b2] = True
    X_wild = int((passed & ~inblock).sum())
    block_cost = max(1, len(blocks)) ** 2 * int(math.log2(max(s, 2)) ** 2)
    total = mc_cost + X_wild + block_cost
    return total, X_wild, mc_cost

rng = np.random.default_rng(13)
delta, eta = 0.1, 0.05
print(f"{'kind':>18} {'s':>5} {'X_wild':>10} {'total':>10} {'s^2':>10} {'tot/s^2':>8}")
worstgrow = {}
for kind in ["arith", "doubling", "random-gaps", "two-ap-mix",
             "ap-plus-noise", "half-ap-half-wild", "short-runs"]:
    tots = []
    for s in [500, 1000, 2000]:
        x = make(kind, s, rng)
        total, Xw, mc = pruned_cost(kind, x, x, delta, eta)
        tots.append(total)
        print(f"{kind:>18} {s:>5} {Xw:>10} {total:>10} {s*s:>10} {total/(s*s):>8.3f}")
    worstgrow[kind] = tots[2] / tots[1]
print()
for kind, g in worstgrow.items():
    print(f"{kind:>18}: growth {g:.2f}  (2.0 linear, 4.0 quadratic)")
# HONEST findings: (a) the prune alone is defeated by near-arithmetic
# noise (random-gaps: X_wild reaches s^2); (b) curved families are
# prune-sparse. Documenting both, not hiding (a) behind cost dilution.
assert worstgrow["doubling"] < 3.0, "curved family must stay subquadratic"
assert worstgrow["random-gaps"] > 2.5, \
    "documenting: near-arithmetic noise defeats the prune alone"
print("pruned-merge probe: prune handles curvature; noise needs fits (documented)")
