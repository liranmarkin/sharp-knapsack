# Probe: how far below their log-concave (Chernoff) envelope do subset-sum
# count arrays dip, and what expected retry factor does tilted-rejection
# split-sampling pay at queries drawn from the actual sampling process?
#
# For a node with children arrays fl, fr and parent c = fl (*) fr:
#   retries(s) = min_theta  Ml(th)*Mr(th)*e^(th*s) / c(s)
# (theta over a grid; exact bigint/log arithmetic via floats of logs).
# We report the QUERY-WEIGHTED mean over s ~ c(s)[s<=t] (what the sampler
# pays), and the max over support (worst adversarial query).
import math, random
from functools import reduce

def counts(ws):
    f = {0: 1}
    for w in ws:
        g = dict(f)
        for s, v in f.items():
            g[s + w] = g.get(s + w, 0) + v
        f = g
    L = max(f)
    return [f.get(s, 0) for s in range(L + 1)]

def conv(a, b):
    c = [0] * (len(a) + len(b) - 1)
    for i, va in enumerate(a):
        if va:
            for j, vb in enumerate(b):
                c[i + j] += va * vb
    return c

def logf(a):
    return [math.log(v) if v else None for v in a]

def retry_stats(fl, fr, cap=None):
    c = conv(fl, fr)
    if cap is None: cap = len(c) - 1
    la, lb = logf(fl), logf(fr)
    # theta grid: enough range to tilt mass anywhere
    span = max(len(fl), len(fr))
    thetas = [0.0] + [math.copysign(2.0 ** k, sgn) / span
                      for k in range(-6, 14) for sgn in (1, -1)]
    Ms = []
    for th in thetas:
        Ml = max(v - th * i for i, v in enumerate(la) if v is not None)
        Ml += math.log(sum(math.exp(v - th * i - Ml) for i, v in enumerate(la) if v is not None))
        Mr = max(v - th * i for i, v in enumerate(lb) if v is not None)
        Mr += math.log(sum(math.exp(v - th * i - Mr) for i, v in enumerate(lb) if v is not None))
        Ms.append((th, Ml + Mr))
    tot = sum(c[s] for s in range(min(cap, len(c) - 1) + 1))
    wmean = 0.0; worst = 0.0
    for s in range(min(cap, len(c) - 1) + 1):
        if c[s] == 0: continue
        lc = math.log(c[s])
        lr = min(M + th * s for th, M in Ms) - lc   # log expected retries
        r = math.exp(min(lr, 700))
        worst = max(worst, r)
        wmean += (c[s] / tot) * r
    return wmean, worst

def split_stats(ws, cap_frac=0.6, name=""):
    random.shuffle(ws)
    mid = len(ws) // 2
    fl, fr = counts(ws[:mid]), counts(ws[mid:])
    cap = int(cap_frac * sum(ws))
    wmean, worst = retry_stats(fl, fr, cap)
    print(f"{name:34s} n={len(ws):3d}  E[retries]={wmean:10.2f}   max-over-support={worst:12.1f}")

rng = random.Random(1)
n = 30
split_stats([rng.randint(1, 200) for _ in range(n)], name="random uniform [1,200]")
split_stats([rng.randint(100, 200) for _ in range(n)], name="bounded-ratio [100,200]")
split_stats([1]*(n//2) + [50]*(n//2), name="two-scale {1,50} (valley maker)")
split_stats([1]*(n//3) + [37]*(n//3) + [1000]*(n//3), name="three-scale {1,37,1000}")
split_stats([2**i for i in range(20)], name="powers of two (flat f=1)")
split_stats([2**i for i in range(12)] + [1]*12, name="powers-of-2 + unit block")
split_stats([7]*(n//2) + [11]*(n//2), name="two coprime multiplicities")
split_stats([50]*(n), name="all equal (binomial)")
split_stats([rng.choice([1,2,3,997,998,1000]) for _ in range(n)], name="clustered two-band")
# adversarial: deep-valley attempt - periodic {1^k, K^k} inside ONE child
ws = [1]*10 + [500]*10 + [rng.randint(1,1000) for _ in range(10)]
split_stats(ws, name="periodic valleys + noise")
