# The witness sampler: proof document

A faster FPRAS for #Knapsack, obtained by reimplementing the sampling stage
of Feng-Jin (SODA 2025, arXiv 2410.22267) on top of their own construction.
Notation follows their paper: D is the level base (their eq. (37),
D ≥ (2n+1)²/δ), per-merge arrays A, B are the prefix-maxed level arrays,
u, v the residual weight arrays with entries in {0} ∪ [1, D), C their
(max,+)-convolution and w the weighted witness counts (their Theorem 6.1).

## Theorem (candidate)

The Feng-Jin FPRAS for #Knapsack can be implemented in total time

    Õ(n^1.5 + min(n·√ℓ, n²/ℓ)·ε^-2)  ≤  Õ(n^1.5 + n^{4/3}·ε^-2),

where ℓ is the instance's popular-class parameter (their Lemma 3.1), with
the same (1±ε)-approximation guarantee. This is never worse than their
Õ(n^1.5·ε^-2) and strictly better whenever ε = o(1).

## Lemma 1 (exact witness decomposition - the linchpin)

*For every merge and every fine position s, the stored merged value
h(s) = D^{C[s]}·w[s] satisfies*

    h(s) = Σ_{(x,y): x+y=s, A[x]+B[y]=C[s]} f(x)·g(y),

*where the sum is over pairs with u[x], v[y] > 0.*

Proof. By Theorem 6.1, w[s] = Σ_{x: A[x]+B[s−x]=C[s]} u[x]v[s−x]. On any
pair in this sum with u[x],v[y] > 0, u[x] = f(x)·D^{−A[x]} and
v[y] = g(y)·D^{−B[y]} (definition of u, v: residuals at prefix-max-attaining
positions), so u[x]v[y]·D^{C[s]} = f(x)g(y)·D^{C[s]−A[x]−B[y]} = f(x)g(y)
by the witness condition A[x]+B[y] = C[s]. ∎  (Machine-checked:
`witness_product_identity` in `lean/SharpKnapsack/WitnessSampler.lean`.)

Consequence: a sampler that (i) draws each node's fine position s
proportionally to the stored array, and (ii) splits s across children
proportionally to f(x)·g(y) over attaining pairs, **factorizes the stored
arrays exactly**. It samples the same tree measure ν that Feng-Jin's own
analysis compares to the uniform distribution; their TV bound
TV(ν, uniform-over-solutions) applies verbatim. The only new TV terms are
(a) the per-merge output rounding of h to log(1/δ)+O(1) bits - a pointwise
(1±δ) factor on the s-marginal, ≤ 2δ TV per visited merge, total
Õ(N·k·log(m)·δ) = negligible at their δ; and (b) nothing else - all draws
below are exactly proportional.

## Lemma 2 (diagonal domination)

*If levels are multiples of 3 (their mod-3 piece decomposition) then, at
every s, pairs with A[x]+B[s−x] < C[s] carry mass
Σ f(x)g(s−x) ≤ δ·(attaining mass), provided s+1 ≤ δ·D.*

Proof. A non-attaining pair has level sum ≤ C[s]−3 (multiples of 3), so
f(x)g(y) < D^{A+1}·D^{B+1} ≤ D^{C[s]−1}. There are ≤ s+1 diagonal pairs, so
the non-attaining mass is < (s+1)·D^{C[s]−1} ≤ δ·D^{C[s]}. Any attaining
pair has f(x)g(y) ≥ D^{A}D^{B} = D^{C[s]}. ∎  (Machine-checked:
`diagonal_witness_domination`, same file; validated empirically in
`experiments/test_witness_sampler.py`.)

This means the sampler may work with attaining pairs only; the excluded
mass is the same ≤ δ-fraction their eq. (41) already charges.

## The sampler

One sample, root capacity t (shared by all N samples):

1. **Root draw**: coarse weight z ∝ f̂_root(z)·[z ≤ t] - prefix sums +
   binary search, O(log). The ≤-constraint exists only here.
2. **De-rounding**: at any node, given its coarse weight z, draw the fine
   (children-sum-grid) position s ∝ h(s) over the preimage interval of z.
   Position rounding is a monotone floor, so the preimage is a contiguous
   interval: an interval-restricted 1D draw, O(log). No subtractions.
3. **Split draw at fine s**: sample the attaining pair (x, y = s−x)
   ∝ u[x]v[y], by:
   a. enumerate active level rectangles (a, C[s]−a), ≤ M_u of them, with
      (2±)-accurate masses from sub-level class counts (see 3b);
   b. per rectangle, per sub-level class pair (i,j) ∈ polylog², the count
      |X_i ∩ (s−Y_j) ∩ (rectangle's diagonal range)| comes from FFT
      correlation arrays (global, per node, built at construction in
      Õ(L·polylog)) prefix-restricted by the lazy dyadic-pair structure;
   c. select rectangle and class ∝ 2^{i+j}·count, select x uniformly in
      the class intersection by rank (dyadic descent), accept with
      probability u[x]v[s−x]/2^{i+j+2} - exact, ≤ 4 expected retries
      (validated in `experiments/test_witness_sampler.py`).
4. **Recurse** into both children with their exact weights x and y; skip a
   child whose weight is 0 and whose ∅-stratum is trivial (the ∅-split
   pruning; validated distribution-exact). A sample visits only the
   path-union of its k contributing leaves.

## Lemma 3 (lazy amortization)

Rank-selection descends dyadic x-intervals; a needed dyadic-pair
correlation conv(1_{X_i∩T}, 1_{Y_j∩T'}) is computed on first use
(Õ(2^k) for level-k pieces) and memoized. Unconditionally, the number of
distinct level-k pairs ever touched is ≤ min(#draws·O(1), (L/2^k)²), so
the total build cost is ≤ Σ_k min(N_u·2^k, L_u²/2^k)·polylog
≤ Õ(L_u·√N_u) per node (AM-GM at the crossover; machine-checked:
`lazy_amortization`). Summed over the tree this is Õ(ℓ·√(N·k̄)) ≤
Õ(ℓ√n/ε), absorbed by the main terms.

## Cost ledger

- Construction: their Õ(n^1.5), plus Õ(L·polylog) per node for prefix
  sums, class sets, global correlations, RMQ - absorbed. C and w are
  already computed by their Theorem 6.1; we retain them.
- Per split-draw: Õ(M_u·polylog) with M_u = Õ(subtree items/polylog)
  levels, capped by the plain scan Õ(L_u): per-draw
  Õ(min(M_u, L_u)) = Õ(min(n_m/2^h, ℓ/2^{h/2})) at depth h.
- Per sample (k contributing leaves, pruned path-union):
  Σ_h min(2^h, k)·min(n_m/2^h, ℓ/2^{h/2}) = Õ(min(n_m, ℓ√k)).
- Total sampling: N = Õ(n/(ℓε²)) samples:
  Õ(min(n²/ℓ, n√ℓ)·ε^-2), maximized at ℓ = n^{2/3} giving n^{4/3}·ε^-2
  (machine-checked collapse: `ledger_collapse`: min(n√ℓ, n²/ℓ)³ ≤ n⁴).
- Second phase (their §5.4): the same tree/merge structure over I₀ with
  N' = Õ(ε^-2) samples; identical treatment, per-sample
  Õ(min(|I₀|, |I₀^j|-scale)) ≤ absorbed by n^{4/3}ε^-2.
- Weight classes: O(log T) = polylog classes; per-sample costs add across
  visited classes, absorbed in Õ(·).

## What remains before this is a theorem

1. A line-by-line pass over Feng-Jin's Lemmas 4.6/4.7 and §5.3-5.4
   substituting this query procedure, confirming their TV statements are
   used only through "the sampler factorizes the stored arrays" - Lemma 1
   is engineered to make this true, but the bookkeeping must be written.
2. The second-phase ledger in full detail.
3. Precision/word-model accounting for the FFT correlations (integer
   0/1-array convolutions - exact, no floating-point issues).

None of these looks structural. The full Lean verification of the
randomized sampler (TV distance, random primes, FFT) is a months-scale
project and out of scope for now; the four load-bearing new lemmas are
machine-checked today in `lean/SharpKnapsack/WitnessSampler.lean`.
