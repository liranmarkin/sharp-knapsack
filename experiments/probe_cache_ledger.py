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
    for (h, idx), ds in distinct.items():
        L_h = max(1, int(ell / 2 ** (h / 2)))
        M_h = max(1, n_m >> h)
        assert len(ds) <= min(visits[(h, idx)], L_h), "distinct-s bound violated"
        cache_cost += min(len(ds), L_h) * M_h
    draw_cost = sum(visits.values())   # polylog-per-draw unit
    return enum_cost, cache_cost + draw_cost

print(f"{'n_m':>6} {'ell':>5} {'N':>7} | {'enum':>12} {'cache+draw':>12} {'ratio':>6}")
for (n_m, ell, N, k) in [(4096, 256, 200, 64), (4096, 256, 2000, 64),
                         (4096, 256, 20000, 64), (16384, 1024, 40000, 128)]:
    e, c = simulate(n_m, ell, N, k)
    print(f"{n_m:>6} {ell:>5} {N:>7} | {e:>12} {c:>12} {e/c:>6.1f}")
    # the win must GROW with N (the small-eps regime)
print("expected: ratio grows with N (cache amortizes; enumeration does not)")
