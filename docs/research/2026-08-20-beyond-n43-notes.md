# Beyond n^{4/3}: the amortized-alias attack

Branch: `beyond-n43`. Goal: strictly dominate the witness-sampler bound
Õ(n^1.5 + min(n√ℓ, n²/ℓ)·ε⁻²) ≤ Õ(n^1.5 + n^{4/3}ε⁻²).

## The bottleneck being attacked

The n^{4/3} kink comes from the per-draw cost min(M_u, L_u): at the
crossover band (ℓ ≈ n^{2/3}) the rectangle enumeration costs
Θ(n^{2/3}) per draw. Killing it to polylog per draw would give
Õ(n^{1.5} + n·ε⁻²) uniformly; that remains blocked by the LM-storage
tradeoff documented on `beat-feng-jin`.

## The new observation: distinct positions are array-bounded

The position s queried at node u is an index of u's stored array, so the
number of DISTINCT (u, s) pairs over the whole run is at most
min(N_u, L_u) - even when the node is visited N_u ≫ L_u times. Building
a per-(u, s) alias table over the active rectangles on first visit
(cost Õ(M_u): ≤ M_u rectangles, each mass in polylog via the correlation
tables) makes every subsequent draw at (u, s) cost polylog.

## The new ledger

Sampling = cache builds + draws:
- draws: Õ(N·k·polylog) = Õ(n·ε⁻²)   [pruned visits, polylog each]
- cache: Σ_u min(N_u, L_u)·M_u ≤ both
  (B) Σ_u N_u·M_u = Õ(N·n) = Õ(n²/(ℓ·ε²))          [rebuild every visit]
  (C) Σ_u L_u·M_u = Σ_h 2^h·(ℓ/2^{h/2})(n_m/2^h)
      = Õ(ℓ·n_m) per class = Õ(ℓ·n)                 [ε-FREE - the new mode]
Plus the old scan mode (A) = Õ(n√ℓ·ε⁻²) (never cache; never worse).

max over ℓ of min(A, B, C):
- ε ≥ n^{-1/6}: worst ℓ = n^{2/3}, min(A,B) = n^{4/3}ε⁻² ≤ C - unchanged.
- ε < n^{-1/6}: worst at B = C: ℓ* = √n/ε, value n^{1.5}/ε
  (A(ℓ*) = n^{5/4}ε^{-5/2} ≥ n^{1.5}ε⁻¹ exactly when ε ≤ n^{-1/6} ✓).

TOTAL: Õ(n^{1.5} + min(n^{4/3}·ε⁻², n^{1.5}·ε⁻¹) + n·ε⁻²).

Domination: ≤ the old bound for every (ℓ, ε); strictly below it for all
ε < n^{-1/6}; tends to the per-sample-optimal n·ε⁻² as ε → 0
(equal to it for ε ≤ n^{-1/2}).

## Honest limits, stated up front

1. At ε ≥ n^{-1/6} the bound is unchanged (n^{4/3}ε⁻²); at ε = Θ(1) it
   still ties Feng-Jin at Õ(n^{1.5}). Beating THAT is the field's stated
   open problem (near-linear FPRAS; the (max,+)-convolution frontier for
   the construction) - not claimed here.
2. Space grows to Õ(min(N·n, n·ℓ)) for the caches (at ℓ* = √n/ε this is
   n^{1.5}/ε words) - a real trade-off the old sampler does not pay.
3. Cost unit as before: the witness-oracle machinery (their Thm 6.1)
   realizing polylog rectangle-mass lookups.

## Checks

Key accounting to validate empirically before proving:
distinct-s per node ≤ min(visits, L_u), and the mode-C sum tracking
Õ(ℓ·n) on simulated visit patterns.

## Night addendum: v2 and the dead ends beyond it

v2 landed: builds enumerate at most min(M_u, L_u) rectangles, mode
C' = Õ(ℓ²), total Õ(n^1.5 + min(n^{4/3}ε^{-4/3}, n²) + n·ε⁻²).
Tightness check: at the adversarial ℓ = (n²/ε²)^{1/3} the two per-node
crossovers (visits vs positions, levels vs positions) COINCIDE, and the
true sum Σ_u min(N_u,L_u)·min(M_u,L_u) concentrates at that level and
realizes n^{4/3}ε^{-4/3} - the accounting is tight for this schedule;
further progress needs a new mechanism, not a finer sum.

Dead ends probed for killing the residual term (all hit the L·M
information wall):
1. Prefix-window witness queries W(s, [y1,y2]) for binary-search
   sampling: a fresh (s, window) query has no small certificate;
   their Thm 6.1 magic is batch-only (all s at once via FFT).
2. Random-prime/root-of-unity sketches: give evaluations of
   Σ ζ^{A+B}, not per-diagonal extraction, and never sampling.
3. Separable rejection via the shared diagonal factor D^c: the level
   part IS flat on the anti-diagonal, but residuals span [1, D) with
   log D = polylog BITS, so residual ratios are quasi-polynomial -
   flat rejection dies; factor-2 residual classes bring back
   per-(class-pair, level-pair) tables = the wall.
4. Incremental alias across adjacent positions: masses at s and s+1
   are unrelated (independent corr lookups).
5. Fewer distinct positions per node: traffic is mass-proportional,
   adversary-controlled; Θ(min(N_u, L_u)) is realizable.

Open sub-problem (the one that would give uniform Õ(n^1.5 + n·ε⁻²)):
answer fresh single-position witness-structure queries in o(min(M, L)),
or find an ε-free build mode below ℓ².
