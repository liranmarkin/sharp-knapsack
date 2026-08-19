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

# --- v3: lazy dyadic doubling ---------------------------------------------
# A node deepens its block-merge tree only as visits double (depth d keeps
# 4^d <= visits), paying 2^d * L per deepening; a draw then binary-searches
# stored block weights and pays L/2^d + O(polylog). Verify per-node
# amortization (build <= 6*L*sqrt(V) + 2*L) and that pure-v3 beats pure-v2
# in the mid-band (N*k below l^2).
def doubling_node(L, V):
    d, build, draw = 0, 0, 0
    for v in range(1, V + 1):
        while 4 ** (d + 1) <= v:
            d += 1
            build += 2 ** d * L
        draw += max(1, L >> d) + 1
    assert build <= 6 * L * math.sqrt(V) + 2 * L, (L, V, build)
    return build, draw

def simulate_v3(n_m, ell, N, k):
    depth = max(1, int(math.log2(max(2, n_m))))
    visits = defaultdict(int)
    for _ in range(N):
        leaves = rng.sample(range(2 ** depth), min(k, 2 ** depth))
        nodes = set()
        for leaf in leaves:
            for h in range(depth + 1):
                nodes.add((h, leaf >> (depth - h)))
        for nd in nodes:
            visits[nd] += 1
    v2_cost, v3_cost = 0, 0
    for (h, idx), V in visits.items():
        L_h = max(1, int(ell / 2 ** (h / 2)))
        M_h = max(1, n_m >> h)
        v2_cost += min(V, L_h) * min(M_h, L_h) + V
        b, dr = doubling_node(L_h, V)
        v3_cost += b + dr
    return v2_cost, v3_cost

print()
print(f"{'n_m':>6} {'ell':>5} {'N':>7} | {'v2':>12} {'v3':>12} {'v2/v3':>6}")
# v3's win regime is sqrt(N*k) well below l (its constants are ~10x):
# there the block tree stays shallow while v2 still pays min(M,L) per
# fresh position on the wide top levels
mid = []
for (n_m, ell, N, k) in [(65536, 4096, 500, 8), (65536, 4096, 2000, 8)]:
    c2, c3 = simulate_v3(n_m, ell, N, k)
    mid.append(c2 / c3)
    print(f"{n_m:>6} {ell:>5} {N:>7} | {c2:>12} {c3:>12} {c2/c3:>6.1f}")
assert mid[-1] > 1.5, "v3 must beat v2 in its regime"
assert mid[-1] > mid[0], "v3 advantage must grow with N"
print("all dyadic-doubling assertions passed (v3)")
