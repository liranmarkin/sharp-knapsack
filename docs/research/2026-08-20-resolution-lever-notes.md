# The resolution lever: Õ(n^1.5 + n·ε⁻²) uniformly

Branch: `resolution-lever`. One mechanism, replacing v1-v3 of
`beyond-n43` entirely.

## The idea

Everything so far accepted Feng-Jin's coupling "grid step ≈ T/ℓ²",
which makes the rounded superset over-count by 1/p = Õ(n/ℓ) and forces
N = Õ(n/(ℓε²)) samples; v1-v3 existed to make those samples cheap.
Instead: run the SAME pipeline at grid step δ = T/(ℓ·n·polylog) - fine
enough that the TOTAL accumulated rounding error E_max ≤ n·polylog·δ
stays below one band width T/ℓ. Then:

- Round-down gives Ω ⊆ Ω' (no false negatives), and
  Ω' \ Ω ⊆ band(T, E_max) ⊆ band(T, T/ℓ), whose mass is Õ(h)·|Ω| by
  their Lemma 3.3 - ALREADY MACHINE-CHECKED as `lemma_33`, which talks
  only about true weights and is completely orthogonal to rounding.
- So p = |Ω|/|Ω'| ≥ 1/polylog and N = Õ(ε⁻²).

## Why this was not available to Feng-Jin (and is to us)

The boost multiplies every array length by F = n·polylog. Their query
(Lemma 4.7) costs Õ(L·√n)-scale - it READS the arrays, so boosting
destroys their sampling term. Our pruned witness scan costs
Õ(min(M_u, L_u)) per draw with M_u = subtree LEVELS - resolution-free.
Per sample: Σ_path-union M_h = Õ(n_m) ≤ Õ(n), independent of F.
The lever is worthless with their query and decisive with ours.

## The ledger

- Construction: per-merge Õ(L·√M) (their Thm 6.1 / bounded-monotone
  (max,+), parametric in L). At boost F:
  Σ_h 2^h·(Fℓ/2^{h/2})·√(n_m/2^h) = F·ℓ·√n_m·depth. Full crank
  F = n/ℓ: Õ(n·√n) = Õ(n^1.5) - INDEPENDENT of ℓ. Storage same.
- Sampling: N = Õ(ε⁻²) × per-sample Õ(n) = Õ(n·ε⁻²).
- TOTAL: Õ(n^1.5 + n·ε⁻²), uniformly in ε and ℓ. No caches, no
  doubling, no alias structures - the plain pruned scan suffices at
  ε⁻² samples.

vs fprasApex: ≤ everywhere; strictly better on all ε ∈ (n^{-1/2},
n^{-1/6}) (up to n^{1/8} at ε = n^{-1/4}); closes the open sub-problem
(the residual ε-term is GONE - this is the optimal shape: construction
+ output-optimal sampling). vs Feng-Jin: strictly better for every
ε ≤ 1/polylog; ties Õ(n^1.5) at ε = Θ(1) (their §1.3 open problem).

## Risks checked against ground truth

1. Band lemma at gap T/ℓ: `lemma_33` hypothesis `hgap : gap·ℓ ≤ T` ✓;
   all other hypotheses are instance-side, resolution-free ✓.
2. One-sidedness: rounding down at every node ⟹ rounded ≤ true ⟹
   Ω ⊆ Ω' ✓ (needs W' ≤ W pointwise and monotone merges - to prove).
3. Thm 6.1 at boosted lengths: their statement is parametric in L;
   reliance unchanged ✓.
4. Per-draw resolution-freeness: level enumeration touches M_u levels,
   not L_u positions; corr tables are construction-side (F·L·polylog,
   absorbed) ✓.
5. E_max accounting: error accumulates per merge on each item's path;
   ≤ depth·δ per partial sum, ≤ n·depth·δ per mask - the probe
   validates the constant.

## Addendum: the rank-selection subtlety (caught in self-review)

PR #1's lazy dyadic rank-selection amortizes at Õ(L·√N) per node -
LENGTH-dependent, which at boost would re-introduce an n^{1.5}·ε⁻¹
term (Cauchy-Schwarz over visited nodes: F·ℓ·√(N·k) = n^{1.5}/ε).
Resolution: at N = Õ(ε⁻²) the lazy structures are unnecessary. Build
STATIC per-(level, residual-class) sorted position arrays with prefix
counts at construction time: cost Õ(Σ_u L_u·polylog) = Õ(F·ℓ·√n) =
Õ(n^{1.5}) at full crank - the same order as the arrays themselves.
They support both piece-mass queries (prefix lookups on the 9-piece
rectangle decomposition) and within-level rank selection (binary
search) in polylog per query. Every draw is then polylog end-to-end
except the level enumeration Õ(M_u), which `scan_ledger` covers. The
lever result therefore DROPS `lazy_amortization` from the load-bearing
set - one more simplification.
