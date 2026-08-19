# Validation tests for the witness sampler (docs/witness-sampler.md).
# Self-contained, deterministic, no dependencies; exits nonzero on failure.
#
#   T1  witness-diagonal split draw is distribution-exact (TV vs brute force)
#       and the witness (attaining) mass is essentially the whole diagonal
#   T2  level compression: #levels is far below the array length
#   T3  sub-level class draw is exact with <= 4 expected retries
#   T4  attaining-mass domination under 3-separated levels
#   T5  the ∅-split pruned tree sampler is distribution-exact
import itertools
import math
import random
from collections import Counter

rng = random.Random(11)


def counts(ws):
    f = {0: 1}
    for w in ws:
        g = dict(f)
        for s, v in f.items():
            g[s + w] = g.get(s + w, 0) + v
        f = g
    return [float(f.get(i, 0)) for i in range(max(f) + 1)]


def tv(c1, c2, n):
    keys = set(c1) | set(c2)
    return 0.5 * sum(abs(c1.get(k, 0) / n - c2.get(k, 0) / n) for k in keys)


# ---------------------------------------------------------------- T1 + T2
D = 2.0 ** 8


def make_levels(f):
    As, A, u = [], [], []
    best = -1
    for x, fx in enumerate(f):
        ax = math.floor(math.log(fx, D)) if fx > 0 else -1
        As.append(ax)
        best = max(best, ax)
        A.append(best)
        u.append(fx / D ** best if (fx > 0 and ax == best) else 0.0)
    return As, A, u


def intervals(A):
    iv, i = {}, 0
    while i < len(A):
        j = i
        while j + 1 < len(A) and A[j + 1] == A[i]:
            j += 1
        if A[i] >= 0:
            iv[A[i]] = (i, j)
        i = j + 1
    return iv


class Pref:
    def __init__(self, a):
        self.p = [0.0]
        for v in a:
            self.p.append(self.p[-1] + v)

    def range(self, i, j):
        return self.p[j + 1] - self.p[i] if j >= i else 0.0


def draw_in_pair(u, v, I, J, s, Pu):
    # x in the pair's diagonal range ~ u[x]*v[s-x]: propose x ~ u, accept v/Vmax
    lo, hi = max(I[0], s - J[1]), min(I[1], s - J[0])
    Vmax = max(v[J[0]:J[1] + 1])
    tot = Pu.range(lo, hi)
    if tot <= 0:
        return None
    while True:
        t = rng.random() * tot
        a, b = lo, hi
        while a < b:
            m = (a + b) // 2
            if Pu.range(lo, m) >= t:
                b = m
            else:
                a = m + 1
        if v[s - a] > 0 and rng.random() < v[s - a] / Vmax:
            return a


def witness_draw(f, g, s):
    # split-draw at fine position s: level-rectangle enumeration, then in-pair
    Asf, Af, u = make_levels(f)
    Asg, Ag, v = make_levels(g)
    If, Ig = intervals(Af), intervals(Ag)
    Pu = Pref(u)
    xr = range(max(0, s - len(g) + 1), min(len(f), s + 1))
    Cs = max(Asf[x] + Asg[s - x] for x in xr if u[x] > 0 and v[s - x] > 0)
    pairs = []
    for a, I in If.items():
        if Cs - a in Ig:
            J = Ig[Cs - a]
            lo, hi = max(I[0], s - J[1]), min(I[1], s - J[0])
            if lo <= hi:
                w = Pu.range(lo, hi) * max(v[J[0]:J[1] + 1])
                if w > 0:
                    pairs.append((w, I, J))
    while True:
        t = rng.random() * sum(w for w, _, _ in pairs)
        acc = 0.0
        for w, I, J in pairs:
            acc += w
            if t <= acc:
                x = draw_in_pair(u, v, I, J, s, Pu)
                if x is not None:
                    return x
                break


wl = [rng.randint(1, 40) for _ in range(12)]
wr = [rng.randint(1, 40) for _ in range(12)]
f, g = counts(wl), counts(wr)
s = (len(f) + len(g)) // 3
Asf, Af, u = make_levels(f)
Asg, Ag, v = make_levels(g)
xr = range(max(0, s - len(g) + 1), min(len(f), s + 1))
Cs = max(Asf[x] + Asg[s - x] for x in xr if u[x] > 0 and v[s - x] > 0)
target = {x: u[x] * v[s - x] for x in xr
          if u[x] > 0 and v[s - x] > 0 and Asf[x] + Asg[s - x] == Cs}
Z = sum(target.values())
N = 30000
c = Counter()
for _ in range(N):
    c[witness_draw(f, g, s)] += 1
t1 = tv(c, Counter({x: N * m / Z for x, m in target.items()}), N)
frac = sum(f[x] * g[s - x] for x in target) / sum(f[x] * g[s - x] for x in xr)
assert t1 < 0.06, f"T1 exactness failed: TV={t1:.4f}"
assert frac > 0.99, f"T1 witness fraction failed: {frac:.4f}"
print(f"T1 witness split draw: TV={t1:.4f} (<0.06), witness fraction={frac:.4f} (>0.99)")

nlv = 96
fc = counts([rng.randint(100, 200) for _ in range(nlv)])
grid = max(1, len(fc) // (4 * nlv))
fr = [sum(fc[i] for i in range(j * grid, min((j + 1) * grid, len(fc))))
      for j in range((len(fc) + grid - 1) // grid)]
levels = len(intervals(make_levels(fr)[1]))
assert levels <= nlv and levels < len(fr) // 4, f"T2 failed: {levels} vs L={len(fr)}"
print(f"T2 level compression: {levels} levels vs array length {len(fr)} ({nlv} items)")

# ---------------------------------------------------------------- T3
def sublevel_draw(u, v, s, lo, hi):
    classes = {}
    for x in range(lo, hi + 1):
        y = s - x
        if 0 <= y < len(v) and u[x] > 0 and v[y] > 0:
            key = (int(math.log2(u[x])), int(math.log2(v[y])))
            classes.setdefault(key, []).append(x)
    keys = list(classes)
    wts = [2.0 ** (i + j) * len(classes[(i, j)]) for (i, j) in keys]
    r = 0
    while True:
        r += 1
        (i, j) = rng.choices(keys, wts)[0]
        x = rng.choice(classes[(i, j)])
        if rng.random() < u[x] * v[s - x] / 2.0 ** (i + j + 2):
            return x, r


uu = [2.0 ** (rng.random() * 10) for _ in range(400)]
vv = [2.0 ** (rng.random() * 10) for _ in range(400)]
for k in range(0, 400, 7):
    vv[k] = 2.0 ** 10 - 1e-9          # adversarial spikes
s3, lo, hi = 500, 150, 350
tgt = {x: uu[x] * vv[s3 - x] for x in range(lo, hi + 1) if 0 <= s3 - x < 400}
Z3 = sum(tgt.values())
c3, rt = Counter(), 0
for _ in range(N):
    x, r = sublevel_draw(uu, vv, s3, lo, hi)
    c3[x] += 1
    rt += r
t3 = tv(c3, Counter({x: N * m / Z3 for x, m in tgt.items()}), N)
assert t3 < 0.06, f"T3 exactness failed: TV={t3:.4f}"
assert rt / N < 4, f"T3 retry bound failed: {rt/N:.2f}"
print(f"T3 sub-level draw: TV={t3:.4f} (<0.06), mean retries={rt/N:.2f} (<4)")

# ---------------------------------------------------------------- T4
Dr = 2.0 ** 12
worst = 1.0
for _ in range(20):
    fa = counts([rng.randint(1, 60) for _ in range(11)])
    fb = counts([rng.randint(1, 60) for _ in range(11)])
    for s4 in range(20, min(len(fa) + len(fb) - 2, 600), 23):
        pr = [(fa[x], fb[s4 - x])
              for x in range(max(0, s4 - len(fb) + 1), min(len(fa), s4 + 1))]
        pr = [(a, b) for a, b in pr if a > 0 and b > 0]
        if not pr:
            continue
        lv = [3 * (int(math.log(a, Dr)) + int(math.log(b, Dr))) for a, b in pr]
        top = sum(a * b for (a, b), l in zip(pr, lv) if l == max(lv))
        worst = min(worst, top / sum(a * b for a, b in pr))
assert worst > 0.95, f"T4 attaining domination failed: {worst:.4f}"
print(f"T4 attaining-mass domination: worst fraction={worst:.4f} (>0.95)")

# ---------------------------------------------------------------- T5
class Node:
    __slots__ = ('f', 'left', 'right', 'item')

    def __init__(self, f, left=None, right=None, item=None):
        self.f, self.left, self.right, self.item = f, left, right, item


def build(items):
    if len(items) == 1:
        i, w = items[0]
        if w == 0:
            return Node([2], item=items[0])
        f5 = [0] * (w + 1)
        f5[0], f5[w] = 1, 1
        return Node(f5, item=items[0])
    mid = len(items) // 2
    L5, R5 = build(items[:mid]), build(items[mid:])
    f5 = [0] * (len(L5.f) + len(R5.f) - 1)
    for a, va in enumerate(L5.f):
        if va:
            for b, vb in enumerate(R5.f):
                f5[a + b] += va * vb
    return Node(f5, L5, R5)


def sample_exact(node, target):
    if node.item is not None:
        i, w = node.item
        opts = ([frozenset()] if target == 0 else []) + \
               ([frozenset([i])] if w == target and (w > 0 or target == 0) else [])
        return rng.choice(opts)
    L5, R5 = node.left, node.right
    ymax = min(target, len(L5.f) - 1)
    ws5 = [L5.f[y] * (R5.f[target - y] if target - y < len(R5.f) else 0)
           for y in range(ymax + 1)]
    y = rng.choices(range(ymax + 1), ws5)[0]
    return sample_exact(L5, y) | sample_exact(R5, target - y)


def sample_pruned(node, cap):
    if node.item is not None:
        i, w = node.item
        opts = [frozenset()] + ([frozenset([i])] if w <= cap else [])
        return rng.choice(opts)
    L5, R5 = node.left, node.right
    pref = [0]
    for v5 in R5.f:
        pref.append(pref[-1] + v5)
    ymax = min(cap, len(L5.f) - 1)
    ws5 = [L5.f[y] * pref[min(cap - y, len(R5.f) - 1) + 1] for y in range(ymax + 1)]
    y = rng.choices(range(ymax + 1), ws5)[0]
    Xl = frozenset() if (y == 0 and L5.f[0] == 1) else sample_exact(L5, y)  # prune
    return Xl | sample_pruned(R5, cap - y)


items5 = [(i, rng.randint(3, 6)) for i in range(8)]
root, cap = build(items5), 12
sols = [frozenset(X) for r in range(9) for X in itertools.combinations(range(8), r)
        if sum(w for j, w in items5 if j in X) <= cap]
c5 = Counter()
for _ in range(N):
    c5[sample_pruned(root, cap)] += 1
t5 = tv(c5, Counter({X: N / len(sols) for X in sols}), N)
assert t5 < 0.06, f"T5 pruning exactness failed: TV={t5:.4f}"
print(f"T5 pruned sampler: TV={t5:.4f} (<0.06) over {len(sols)} solutions")

print("all witness-sampler validations passed")
