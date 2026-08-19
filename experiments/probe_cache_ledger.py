# Probe: validate the amortized-alias ledger on simulated sampler traffic.
#   - distinct positions per node never exceed min(visits, L_u)
#   - cache cost  Sum_u min(#distinct_s_u, L_u) * M_u  tracks the predicted
#     min(N*n, l*n) mode and beats the enumeration cost N*min(M,L) when
#     N is large (small eps), on a class-tree schedule L_h = l/2^{h/2},
#     M_h = n_m/2^h.
import math, random
from collections import defaultdict

rng = random.Random(3)

def simulate(n_m, ell, N, k):
    depth = max(1, int(math.log2(max(2, n_m))))
    visits = defaultdict(int)          # node -> visits
    distinct = defaultdict(set)        # node -> distinct positions
    enum_cost = 0
    for _ in range(N):
        # a sample = k random leaves; walk their path-union; positions are
        # random array indices per node (worst case for distinctness)
        leaves = rng.sample(range(2 ** depth), min(k, 2 ** depth))
        nodes = set()
        for leaf in leaves:
            for h in range(depth + 1):
                nodes.add((h, leaf >> (depth - h)))
        for (h, idx) in nodes:
            L_h = max(1, int(ell / 2 ** (h / 2)))
            M_h = max(1, n_m >> h)
            s = rng.randrange(L_h)     # position within the node's array
            visits[(h, idx)] += 1
            distinct[(h, idx)].add(s)
            enum_cost += min(M_h, L_h)
    cache_cost = 0
    cache2_cost = 0
    for (h, idx), ds in distinct.items():
        L_h = max(1, int(ell / 2 ** (h / 2)))
        M_h = max(1, n_m >> h)
        assert len(ds) <= min(visits[(h, idx)], L_h), "distinct-s bound violated"
        cache_cost += min(len(ds), L_h) * M_h
        # v2: a build enumerates at most min(M_h, L_h) rectangles - a level
        # present in the array occupies at least one cell
        cache2_cost += min(len(ds), L_h) * min(M_h, L_h)
    draw_cost = sum(visits.values())   # polylog-per-draw unit
    return enum_cost, cache_cost + draw_cost, cache2_cost + draw_cost, \
        cache_cost, cache2_cost

print(f"{'n_m':>6} {'ell':>5} {'N':>7} | {'enum':>12} {'v1':>12} {'v2':>12} {'r1':>6} {'r2':>6}")
r1s, r2s, builds = [], [], []
for (n_m, ell, N, k) in [(4096, 256, 200, 64), (4096, 256, 2000, 64),
                         (4096, 256, 20000, 64), (16384, 1024, 40000, 128)]:
    e, c1, c2, b1, b2 = simulate(n_m, ell, N, k)
    r1s.append(e / c1); r2s.append(e / c2); builds.append((b1, b2))
    print(f"{n_m:>6} {ell:>5} {N:>7} | {e:>12} {c1:>12} {c2:>12} {e/c1:>6.1f} {e/c2:>6.1f}")
assert r1s[1] > 2 and r1s[2] > 2 * r1s[1], "v1 amortization win must grow with N"
assert r1s[3] > 10, "v1 large-instance win must be an order of magnitude"
assert all(r2 >= r1 for r1, r2 in zip(r1s, r2s)), "v2 must dominate v1"
# the rectangle cap min(M,L) bites on the shallow levels: the BUILD cost
# (the part the theory bounds by l^2 instead of l*n) must drop by a real
# factor at scale
assert all(b2 <= b1 for b1, b2 in builds), "v2 builds must never exceed v1"
assert builds[3][0] > 3 * builds[3][1], "v2 build cost must drop at scale"
print("all cache-ledger assertions passed (v1 + v2)")
