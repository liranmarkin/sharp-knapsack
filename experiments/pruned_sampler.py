# Mini Feng-Jin-style tree sampler (bounded-ratio case), exact arithmetic,
# comparing (1) full-tree descent vs (2) pruned descent with empty-split.
# Checks: (a) both produce the EXACT target distribution (uniform over
# {X : w(X) <= cap}); (b) visited-work scaling: full ~ sum of all node array
# lengths, pruned ~ sum over path-union of touched nodes only.
import random, itertools
from collections import Counter

rng = random.Random(7)

class Node:
    __slots__ = ('f', 'left', 'right', 'item', 'L')
    def __init__(self, f, left=None, right=None, item=None):
        self.f = f          # exact count array: f[t] = #subsets of subtree with rounded weight t
        self.left = left; self.right = right; self.item = item
        self.L = len(f)

def build(items):
    # items: list of (id, rounded_weight)
    if len(items) == 1:
        i, w = items[0]
        f = [0]*(w+1); f[0] += 1; f[w] += 1
        if w == 0: f = [2]  # both subsets weigh 0
        return Node(f, item=items[0])
    mid = len(items)//2
    Lc, Rc = build(items[:mid]), build(items[mid:])
    f = [0]*(len(Lc.f)+len(Rc.f)-1)
    for a, va in enumerate(Lc.f):
        if va:
            for b, vb in enumerate(Rc.f):
                f[a+b] += va*vb
    return Node(f, Lc, Rc)

work = 0  # array positions scanned during queries

def sample_full(node, cap):
    # returns set of item ids with rounded subtree weight <= cap, uniform
    global work
    if node.item is not None:
        i, w = node.item
        opts = [(frozenset(), 0)]
        if w <= cap: opts.append((frozenset([i]), w))
        weights = [1]*len(opts)
        work += 2
        pick = rng.choices(range(len(opts)), weights)[0]
        return opts[pick]
    L, R = node.left, node.right
    # draw split y = left weight, prob ∝ fL[y] * FR^<=(cap - y)
    FR = R.f
    pref = [0]*(len(FR)+1)
    for t, v in enumerate(FR): pref[t+1] = pref[t] + v
    ws = []
    ymax = min(cap, len(L.f)-1)
    for y in range(ymax+1):
        rcap = min(cap - y, len(FR)-1)
        ws.append(L.f[y] * pref[rcap+1])
    work += (ymax + 1) + len(FR)
    y = rng.choices(range(ymax+1), ws)[0]
    Xl, wl = sample_full(L, y_exact(L, y))
    # conditioned left weight == y exactly:
    Xl, wl = sample_exact(L, y)
    Xr, wr = sample_full(R, cap - y)
    return (Xl | Xr, wl + wr)

def sample_exact(node, target):
    # uniform subset of subtree with rounded weight EXACTLY target
    global work
    if node.item is not None:
        i, w = node.item
        opts = []
        if target == 0: opts.append(frozenset())
        if w == target and w > 0: opts.append(frozenset([i]))
        if target == 0 and w == 0: opts.append(frozenset([i]))
        pick = rng.choices(range(len(opts)))[0]
        work += 1
        return (opts[pick], target)
    L, R = node.left, node.right
    ws = []
    ymax = min(target, len(L.f)-1)
    for y in range(ymax+1):
        r = target - y
        ws.append(L.f[y] * (R.f[r] if r < len(R.f) else 0))
    work += ymax + 1
    y = rng.choices(range(ymax+1), ws)[0]
    Xl, _ = sample_exact(L, y)
    Xr, _ = sample_exact(R, target - y)
    return (Xl | Xr, target)

def y_exact(node, y): return y

def sample_pruned(node, cap):
    # like sample_full but: draw (empty?, weight) jointly; skip empty subtrees.
    global work
    if node.item is not None:
        i, w = node.item
        opts = [(frozenset(), 0)]
        if w <= cap: opts.append((frozenset([i]), w))
        work += 2
        pick = rng.choices(range(len(opts)))[0]
        return opts[pick]
    L, R = node.left, node.right
    FR = R.f
    pref = [0]*(len(FR)+1)
    for t, v in enumerate(FR): pref[t+1] = pref[t] + v
    ws = []
    ymax = min(cap, len(L.f)-1)
    for y in range(ymax+1):
        rcap = min(cap - y, len(FR)-1)
        ws.append(L.f[y] * pref[rcap+1])
    work += (ymax + 1) + len(FR)
    y = rng.choices(range(ymax+1), ws)[0]
    # left side: weight exactly y ; prune if y==0 AND the only weight-0 subset is empty
    if y == 0 and L.f[0] == 1:
        Xl = frozenset()          # PRUNE: no descent
    else:
        Xl, _ = sample_exact(L, y)
    # right side: weight <= cap - y ; prune iff conditional forces empty... cannot
    # prune "<=" side by weight alone; recurse (still bounded by nonempty portions).
    Xr, wr = sample_pruned(R, cap - y)
    return (Xl | Xr, y + wr)

def tv(c1, c2, N):
    keys = set(c1)|set(c2)
    return 0.5*sum(abs(c1.get(k,0)/N - c2.get(k,0)/N) for k in keys)

# ---- correctness check on a small instance
items = [(i, rng.randint(3, 6)) for i in range(8)]   # bounded-ratio-ish weights
root = build(items)
cap = 12
target = [frozenset(X) for r in range(9) for X in itertools.combinations(range(8), r)
          if sum(w for j,w in items if j in X) <= cap]
uniform = Counter()
N = 40000
cf, cp = Counter(), Counter()
for _ in range(N):
    X, _ = sample_full(root, cap); cf[X] += 1
    X, _ = sample_pruned(root, cap); cp[X] += 1
exact = Counter({X: N/len(target) for X in target})
print(f"target size={len(target)}  TV(full,exact)={tv(cf, exact, N):.4f}  TV(pruned,exact)={tv(cp, exact, N):.4f}")
print("(both should be ~0.01-0.03 = sampling noise at N=40k)")

# ---- work scaling: full vs pruned on larger sparse-solution instances
for n in (64, 128, 256):
    items = [(i, rng.randint(50, 100)) for i in range(n)]
    root = build(items)
    cap = 300   # solutions have <= 6 items => pruning should shine
    global_work = 0
    import builtins
    for label, fn in (("full", sample_full), ("pruned", sample_pruned)):
        globals()['work'] = 0
        for _ in range(30): fn(root, cap)
        print(f"n={n:4d} {label:6s} avg work/sample = {work/30:10.0f}")
