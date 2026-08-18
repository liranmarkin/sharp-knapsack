# End-to-end validation of the sub-level-class split draw:
#   target: x ~ u[x]*v[s-x] over a window, u,v in [1,D)
#   scheme: classes X_i = {x: u[x] in [2^i, 2^(i+1))}, Y_j likewise for v;
#           draw class (i,j) ~ 2^(i+j) * |X_i ∩ (s - Y_j) ∩ win|  (corr from FFT
#           in the real algo; exact counts here), then x uniform in the
#           intersection (rank-selection in the real algo), then accept w.p.
#           u[x]v[s-x] / 2^(i+j+2)  -> exact target, retries <= 4.
# Also validates the attaining-set acceptance under D^-3 level separation.
import math, random
from collections import Counter
rng = random.Random(5)

def sublevel_draw(u, v, s, lo, hi):
    classes = {}
    for x in range(lo, hi + 1):
        y = s - x
        if 0 <= y < len(v) and u[x] > 0 and v[y] > 0:
            i, j = int(math.log2(u[x])), int(math.log2(v[y]))
            classes.setdefault((i, j), []).append(x)
    if not classes: return None, 0
    keys = list(classes)
    wts = [2.0 ** (i + j) * len(classes[(i, j)]) for (i, j) in keys]
    r = 0
    while True:
        r += 1
        (i, j) = rng.choices(keys, wts)[0]
        x = rng.choice(classes[(i, j)])        # rank-selection stand-in
        if rng.random() < u[x] * v[s - x] / 2.0 ** (i + j + 2):
            return x, r

D = 2.0 ** 10
L = 400
u = [2.0 ** (rng.random() * 10) for _ in range(L)]   # arbitrary in [1, D)
v = [2.0 ** (rng.random() * 10) for _ in range(L)]
for k in range(0, L, 7): v[k] = D - 1e-9              # adversarial spikes
s, lo, hi = 500, 150, 350
target = {x: u[x] * v[s - x] for x in range(lo, hi + 1) if 0 <= s - x < L}
Z = sum(target.values())
N = 60000
c = Counter(); rt = 0
for _ in range(N):
    x, r = sublevel_draw(u, v, s, lo, hi)
    c[x] += 1; rt += r
tv = 0.5 * sum(abs(c.get(x, 0) / N - target.get(x, 0) / Z) for x in set(c) | set(target))
print(f"sub-level draw: TV = {tv:.4f} (noise ~0.01-0.02)   mean retries = {rt/N:.2f} (bound 4)")

# attaining-set acceptance under D^-3 separation: mass of level-sum < max
# vs max, on a real count-array diagonal
def counts(ws):
    f = {0: 1}
    for w in ws:
        g = dict(f)
        for k2, cv in f.items(): g[k2 + w] = g.get(k2 + w, 0) + cv
        f = g
    Lm = max(f)
    return [float(f.get(i2, 0)) for i2 in range(Lm + 1)]
Dr = 2.0 ** 8
worst = 1.0
for trial in range(20):
    fa = counts([rng.randint(1, 60) for _ in range(11)])
    fb = counts([rng.randint(1, 60) for _ in range(11)])
    for s2 in range(20, min(len(fa) + len(fb) - 2, 600), 23):
        pairs = [(fa[x], fb[s2 - x]) for x in range(max(0, s2 - len(fb) + 1), min(len(fa), s2 + 1))]
        pairs = [(a, b) for a, b in pairs if a > 0 and b > 0]
        if not pairs: continue
        lv = [3 * (int(math.log(a, Dr)) + int(math.log(b, Dr))) for a, b in pairs]  # 3-separated levels
        mx = max(lv)
        top = sum(a * b for (a, b), l in zip(pairs, lv) if l == mx)
        tot = sum(a * b for a, b in pairs)
        worst = min(worst, top / tot)
print(f"attaining-mass fraction on diagonals: worst over 20x~26 queries = {worst:.4f} (need ~1)")
