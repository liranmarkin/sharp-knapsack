# Prototype of the witness-structured split-draw.
# Target: sample (x,y) ~ u[x]*v[y] over {(x,y): x+y = s, A*[x]+B*[y] = C[s],
# prefix-max attaining}, where u,v in {0} U [1,D), A,B monotone level arrays.
# Cost model: count "operations" = level-pairs touched + rejection retries.
# Validations:
#   V1: exactness - TV between sampled distribution and brute-force target.
#   V2: retry bound - adaptive rejection retries stay polylog on adversarial u,v.
#   V3: level-count compression - #levels << array length on realistic rounded arrays.
import math, random
from collections import Counter

rng = random.Random(11)
D = 2.0 ** 8   # log D = 8 = "polylog"

def make_levels(f):
    # A*[x] = floor(log_D f(x)); A = prefix max; u[x] = f[x]/D^A[x] if attaining
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
    # maximal constant-value intervals of monotone A, keyed by value
    iv = {}
    i = 0
    while i < len(A):
        j = i
        while j + 1 < len(A) and A[j + 1] == A[i]: j += 1
        if A[i] >= 0: iv[A[i]] = (i, j)
        i = j + 1
    return iv

class Pref:
    def __init__(self, a):
        self.p = [0.0]
        for v in a: self.p.append(self.p[-1] + v)
    def range(self, i, j):  # sum over [i, j]
        if j < i: return 0.0
        return self.p[j + 1] - self.p[i]

ops = 0

def draw_in_pair(u, v, I, J, s, Pu, Pv):
    # sample (x,y) ~ u[x]v[y], x in I, y in J, x+y = s ... EXACT diagonal here
    # (diagonal within rectangle: y = s-x, x in [max(I0, s-J1), min(I1, s-J0)])
    global ops
    lo = max(I[0], s - J[1]); hi = min(I[1], s - J[0])
    # adaptive-rejection scheme over x-interval [lo,hi], weight u[x]*v[s-x]:
    # pieces with bound = U(piece)*vmax(piece-image) would need RMQ; for the
    # diagonal case we instead do: propose x ~ u[x] (alias/prefix), accept
    # w.p. v[s-x]/Vmax where Vmax = max v over J. Count retries.
    Vmax = max(v[J[0]:J[1] + 1])
    tot = Pu.range(lo, hi)
    if tot <= 0: return None, 0
    r = 0
    while True:
        r += 1; ops += 1
        t = rng.random() * tot
        a, b = lo, hi          # binary search x with prefix
        while a < b:
            m = (a + b) // 2
            if Pu.range(lo, m) >= t: b = m
            else: a = m + 1
        x = a
        if v[s - x] > 0 and rng.random() < v[s - x] / Vmax:
            return (x, s - x), r
        if r > 10000: return None, r

def witness_draw(f, g, s):
    # full witness split-draw for parent position s (exact-diagonal model)
    global ops
    Asf, Af, u = make_levels(f)
    Asg, Ag, v = make_levels(g)
    If, Ig = intervals(Af), intervals(Ag)
    Pu, Pv = Pref(u), Pref(v)
    # C[s] = max over x+y=s of A*f[x]+A*g[y] (attaining def) - brute here,
    # in the real algo it's precomputed by Thm 6.1.
    Cs = max((Asf[x] + Asg[s - x]) for x in range(max(0, s - len(g) + 1), min(len(f), s + 1))
             if u[x] > 0 and v[s - x] > 0) if True else None
    # enumerate active level pairs (a, Cs - a): ops += #active
    pairs = []
    for a, I in If.items():
        b = Cs - a
        if b in Ig:
            J = Ig[b]
            lo = max(I[0], s - J[1]); hi = min(I[1], s - J[0])
            if lo <= hi:
                ops_local = 1
                globals()['ops'] += 1
                # mass bound for pair: U(I-part) * Vmax-ish; exact diag mass for
                # pair-selection uses U(diag range)*Vmax as proposal weight
                Vmax = max(v[J[0]:J[1] + 1])
                w = Pu.range(lo, hi) * Vmax
                if w > 0: pairs.append((w, I, J))
    if not pairs: return None, 0
    # sample pair ~ bound, then within-pair; reject-loop across pairs for exactness
    W = sum(w for w, _, _ in pairs)
    tries = 0
    while True:
        tries += 1
        t = rng.random() * W; acc = 0.0
        for w, I, J in pairs:
            acc += w
            if t <= acc:
                res, r = draw_in_pair(u, v, I, J, s, Pu, Pv)
                if res: return res, tries
                break
        if tries > 20000: return None, tries

# ---------- V1: exactness on random instance
def counts(ws):
    f = {0: 1}
    for w in ws:
        g = dict(f)
        for k, cv in f.items(): g[k + w] = g.get(k + w, 0) + cv
        f = g
    L = max(f)
    return [float(f.get(i, 0)) for i in range(L + 1)]

wl = [rng.randint(1, 40) for _ in range(12)]
wr = [rng.randint(1, 40) for _ in range(12)]
f, g = counts(wl), counts(wr)
s = (len(f) + len(g)) // 3
# brute target over witness set
Asf, Af, u = make_levels(f); Asg, Ag, v = make_levels(g)
Cs = max(Asf[x] + Asg[s - x] for x in range(max(0, s - len(g) + 1), min(len(f), s + 1)) if u[x] > 0 and v[s - x] > 0)
target = {}
for x in range(max(0, s - len(g) + 1), min(len(f), s + 1)):
    if u[x] > 0 and v[s - x] > 0 and Asf[x] + Asg[s - x] == Cs:
        target[(x, s - x)] = u[x] * v[s - x]
Z = sum(target.values())
N = 30000
c = Counter()
tot_tries = 0
for _ in range(N):
    res, tr = witness_draw(f, g, s)
    c[res] += 1; tot_tries += tr
tv = 0.5 * sum(abs(c.get(k, 0) / N - target.get(k, 0) / Z) for k in set(c) | set(target))
print(f"V1 exactness: TV = {tv:.4f} (noise ~0.01-0.02), mean pair-tries = {tot_tries/N:.2f}")
# witness mass vs full diagonal mass (the delta-truncation check)
full = sum(f[x] * g[s - x] for x in range(max(0, s - len(g) + 1), min(len(f), s + 1)))
wit = sum(f[x] * g[s - x] for (x, _) in target)
print(f"   witness mass fraction of diagonal = {wit/full:.4f} (should be >= 1 - poly/D)")

# ---------- V2: retry scaling on adversarial v (huge in-level ratios)
for name, (uu, vv) in {
    "flat u, spike v": ([1.0] * 512, [1.0] * 511 + [200.0]),
    "geometric v (ratio 1.9)": ([1.0] * 512, [1.9 ** i for i in range(9)] * 57),
    "u spike-left, v spike-right": ([200.0] + [1.0] * 511, [1.0] * 511 + [200.0]),
}.items():
    Pu = Pref(uu)
    I, J = (0, 511), (0, len(vv) - 1)
    rs = []
    for _ in range(300):
        res, r = draw_in_pair(uu, vv, I, J, 600, Pu, None)
        rs.append(r)
    print(f"V2 {name:28s}: mean retries = {sum(rs)/len(rs):8.1f}  max = {max(rs)}")

# ---------- V3: level compression on rounded count arrays
for n in (24, 48, 96):
    ws = [rng.randint(100, 200) for _ in range(n)]
    fc = counts(ws)
    # round to grid ~ sqrt-scale like the real algorithm
    grid = max(1, len(fc) // (4 * n))
    fr = [sum(fc[i] for i in range(j * grid, min((j + 1) * grid, len(fc)))) for j in range((len(fc) + grid - 1) // grid)]
    Asr, Ar, ur = make_levels(fr)
    print(f"V3 n={n:3d}: array length L = {len(fr):5d}, #levels = {len(intervals(Ar)):3d}, items = {n}")
