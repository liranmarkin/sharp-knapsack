# Ground-truth probe: is the subset-count-by-weight array f (coefficients of
# prod (1 + x^{w_i})) log-concave / unimodal? If not, the fast product-sampling
# route for T2 is blocked (no structure to exploit for o(L)-per-node sampling).
import random

def count_array(weights, cap):
    # f[t] = number of subsets with total weight exactly t, t in [0, cap]
    f = [0]*(cap+1); f[0] = 1
    for w in weights:
        for t in range(cap, w-1, -1):
            f[t] += f[t-w]
    return f

def logconcave_violations(f):
    # count t with f[t]^2 < f[t-1]*f[t+1] among the support interior
    v = 0
    for t in range(1, len(f)-1):
        if f[t] > 0 and f[t]*f[t] < f[t-1]*f[t+1]:
            v += 1
    return v

def unimodal_violations(f):
    # a unimodal seq rises then falls; count "descents followed by ascent"
    nz = [x for x in f if x >= 0]
    dirn = 0; v = 0
    prev = f[0]
    seen_desc = False
    for x in f[1:]:
        if x > prev: 
            if seen_desc: v += 1  # ascent after a descent => not unimodal
        elif x < prev:
            seen_desc = True
        prev = x
    return v

rng = random.Random(2025)
print("weight-class-like instances (bounded ratio, weights in (C/l, 2C/l]):")
for trial in range(6):
    n = rng.randint(20, 40)
    lo = rng.randint(30, 60); hi = 2*lo
    weights = [rng.randint(lo, hi) for _ in range(n)]
    cap = sum(weights)
    f = count_array(weights, cap)
    lc = logconcave_violations(f)
    um = unimodal_violations(f)
    supp = sum(1 for x in f if x>0)
    print(f"  n={n} lo={lo} support={supp}  log-concave-violations={lc}  unimodal-violations={um}")

print("\ngeneral instances (mixed weights):")
for trial in range(6):
    n = rng.randint(20, 40)
    weights = [rng.randint(1, 100) for _ in range(n)]
    cap = sum(weights)
    f = count_array(weights, cap)
    lc = logconcave_violations(f)
    um = unimodal_violations(f)
    supp = sum(1 for x in f if x>0)
    print(f"  n={n} support={supp}  log-concave-violations={lc}  unimodal-violations={um}")
