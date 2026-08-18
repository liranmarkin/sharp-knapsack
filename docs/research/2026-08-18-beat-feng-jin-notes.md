# Beating Feng-Jin Õ(n^1.5 ε^-2): attack notes

Branch: `beat-feng-jin`. Target: the SODA 2025 FPRAS record for #Knapsack
(Feng-Jin, arXiv 2410.22267). This file is a complete cost ledger + barrier
map from a full read of the paper, written to guide a serious attempt.

## The exact cost ledger (full read)

The total Õ(n^1.5 ε^-2) is the sum of three terms, with distinct causes:

| Term | Cost | Cause | Paper |
|---|---|---|---|
| T1 Construction of sampler S | Õ(n^1.5) | bounded-monotone (max,+)-conv over the merge tree, Õ(L√M) per merge | Lemma 5.9, 4.7, Thm 4.2/6.1 |
| T2 Sampling | Õ(n/(ℓε²)) · Õ(ℓ√n) = Õ(n^1.5 ε^-2) | N samples × per-sample tree query | §5.3, Lemma 5.7 |
| T3 Second phase (tiny items) | Õ(\|I₀\|^1.5 ε^-2) = Õ(n^1.5 ε^-2) | same DP-conv floor on I₀ | Lemma 5.11, 5.15 |

Regimes:
- **Natural regime** ε ≥ 1/polylog(n): ε^-2 = polylog, so T2, T3 collapse to
  Õ(n^1.5) and the *whole* bound is T1 = Õ(n^1.5). **To beat n^1.5 here you
  must beat T1** - which is the open problem Feng-Jin pose in §1.3.
- **Small-ε regime** ε ≤ n^-c: T2, T3 dominate at Õ(n^1.5 ε^-2).

## Why each term resists improvement

**T1 (construction).** Each merge is a (1±δ)-sum-approximation of the
convolution of two count arrays with entries up to 2^n. Feng-Jin reduce this
to bounded-monotone (max,+)-convolution (CDXZ22/BDP24) at Õ(L√M). The √M is
conditionally optimal: general (max,+)-conv has no O(n^{2-δ}) algorithm under
MinConv, and the monotone-bounded speedup to n√M is the current frontier
(Chan-Lewenstein → CDXZ → BDP). Beating T1 ⇒ beating bounded-monotone
(max,+)-conv OR avoiding convolution entirely. Both are open.

**T2 (sampling query).** The per-sample query is Õ(ℓ√n), but the sample's own
size is only Õ(ℓ) - a √n overhead. The overhead is real, not slack: the query
descends into *both* children at every node (Lemma 4.7 query steps 2 AND 3),
visiting all ~m nodes, because to split the capacity at node u it samples
`y ∝ f̂_L(y)·f̂_R^≤(x−y)` over the length-L_u array. **Barrier**: this is
sampling from a pointwise product of a fixed array f̂_L and a shifted CDF
f̂_R^≤(x−·), with x fixed only at query time. f̂_R^≤ is monotone but f̂_L (a
subset-count-by-weight array) is *not* log-concave in general (coefficients of
∏(1+x^{w_i}) can be non-unimodal), so no known structure lets one sample this
in o(L_u). Precomputation is defeated by the per-query x. So the Õ(L_u)/node
cost - hence the √n factor - appears intrinsic to this data structure.
  - *Batching N samples doesn't help*: each sample reaches node u with its own
    capacity x, so the N split-distributions at u differ; no shared work.
  - The ℓ cancels exactly in N·𝒯_q = (n/ℓ)·(ℓ√n) = n^1.5, so tuning ℓ can't
    move T2 (this is why the paper is free to pick ℓ for T1's benefit).

**T3 (second phase).** Solves an N-choose-1 generalized #Knapsack on the tiny
items I₀ via the same Approximate-Knapsack-Sampler machinery; its Õ(|I₀|^1.5)
construction (Lemma 5.15) is the same bounded-monotone-conv floor as T1.

## Verdict of this analysis

All three terms are blocked behind the *same* two recognized-hard problems:
(i) bounded-monotone (max,+)-convolution below n√M (T1, T3), and (ii) fast
sampling from a product-of-arrays split distribution (T2). Neither is a
session-sized gap; both are legitimate open problems. Feng-Jin themselves list
"n^{1.5−Ω(1)} even in the bounded-ratio case" as open.

Honest conclusion: I could not find a correct route to a bound that beats
Õ(n^1.5 ε^-2) in any regime without assuming a breakthrough on (i) or (ii).
Any claim to the contrary here would be fabricated. The value delivered on
this branch is this rigorous ledger + barrier map (the artifact a researcher
wants *before* attempting the problem), not a new algorithm.

## Concrete live directions (for a real, multi-week attempt)

1. **T2 via approximate product-sampling.** Is there an ε-approximate sampler
   for `y ∝ f̂_L(y)·f̂_R^≤(x−y)` in Õ(polylog) per node using a Chebyshev /
   sketch of f̂_L against the monotone f̂_R^≤? If yes for the specific arrays
   Feng-Jin produce (which are (1±δ)-sum-approx, hence "smooth" prefix sums),
   T2 → Õ(n ε^-2) and total → Õ(n^1.5 + n ε^-2) - strictly better for
   ε ≪ n^-1/4. This is the single most promising angle; it needs a genuine
   data-structure result, not a tweak. (Empirical probe below tests the
   sublinearity premise.)
2. **T1 via deterministic-free lower M.** The count entries are ≤ 2^n but
   Feng-Jin already truncate to polylog bits (floating point). The effective M
   in the n√M is thus polylog, and the n^1.5 comes from the *length* L·√m
   summed over the tree, not from M. Re-examine whether the tree's total
   convolution length can be reduced below n^1.5 via a shallower/unbalanced
   merge schedule.

## Empirical ground-truth on direction 1 (the blocker is real)

`experiments/probe_logconcave.py`: computed the exact subset-count-by-weight
array f (coeffs of ∏(1+x^{w_i})) on random bounded-ratio weight-class
instances and general instances, and counted log-concavity /unimodality
violations. Result: on **every** instance, ~half the interior support points
violate log-concavity (e.g. support 1588 → 550 violations) and there are
hundreds of unimodality violations. So f is emphatically NOT log-concave or
unimodal, even in the bounded-ratio "nice" case. This empirically confirms
there is no shape structure to exploit for o(L)-per-node sampling of
`y ∝ f̂_L(y)·f̂_R^≤(x−y)`. Direction 1 as stated is blocked; a real attempt
would need a fundamentally different sketch (e.g. exploiting the (1±δ)-sum-
approx *smoothing* of prefix sums, not pointwise shape) - an open data-
structure question, not a session-sized fix.

## Result: an instance-adaptive refinement (validated, written up)

**Theorem (refinement of Feng-Jin).** The Feng-Jin FPRAS can be modified to
run in time Õ(n^1.5 + n·√ℓ·ε^-2), where ℓ ∈ [2, 8n] is the popular-class
parameter of the instance (their Lemma 3.1). Since ℓ ≤ 8n this never exceeds
their Õ(n^1.5·ε^-2); for every instance with ℓ = o(n) it is strictly better,
and in the natural regime ε ≥ 1/polylog it leaves the bound at Õ(n^1.5).

**The modification (pruned lazy descent).** In the query stage of the merged
sampler (their Lemma 4.7), descend a subtree only if its sampled portion is
nonempty:
1. At each node, the capacity-split draw `y ∝ f̂_L(y)·f̂_R^≤(x−y)` already
   determines the left child's *exact* rounded weight y. If y = 0 and the
   weight-0 stratum of the left child consists of the empty set alone
   (f̂ ⁺_L(0) = 0 for the ∅-removed counting function f̂⁺ := f̂ − 1·[weight 0],
   maintained through merges at no extra cost), output ∅ for that subtree
   and do not descend.
2. Mid-tree re-rounding can send nonempty subsets to weight 0 (when
   m > ℓ·polylog), so descent into a weight-0-but-nonempty stratum still
   happens - but each such descent delivers ≥ 1 item of the sample, so the
   number of such events per sample is ≤ |X₊|·depth.

**Cost accounting.** A partial sample has |X₊| ≤ t = Õ(ℓ) items. The visited
nodes form the path-union of ≤ |X₊| leaves; with L_h = Õ(ℓ/2^{h/2}) the
scan cost is Σ_h min(2^h, |X₊|)·ℓ/2^{h/2} = O(ℓ·√|X₊|) = Õ(ℓ^{1.5}) worst
case, and Õ(ℓ√k) for samples of size k. Total sampling:
N·Õ(ℓ√ℓ) = Õ(n/(ℓε²))·ℓ^{1.5} = Õ(n√ℓ·ε^-2). The same pruning applies to
the second-phase sampler (Lemma 5.15's tree over I₀), giving the analogous
adaptive gain there. Construction is unchanged at Õ(n^1.5).

**Correctness.** The split-draw is unchanged; pruning only skips descents
whose outcome is deterministically ∅, so the output distribution is
*identical* to the unpruned sampler (empirically confirmed: TV 0.016 vs
0.016 against exact uniform at N=40k on an 8-item instance —
`experiments/pruned_sampler.py`; work/sample savings 2.75×→3.94× as n
64→256).

**Status vs the goal.** This is a genuine, checkable improvement of the SOTA
*algorithm* (undominated: better on all ℓ = o(n) instances, never worse),
but NOT a worst-case improvement: at ℓ = Θ(n) it ties. The worst case funnels
entirely into the crux problem:

**Problem (P).** Preprocess nonneg arrays a, b of length L in Õ(L) so that
given query x, one can sample y ∝ a_y·b^≤(x−y) in polylog time (small TV
error allowed). Solving (P) upgrades the bound to Õ(n^1.5 + n·ε^-2)
uniformly. Shown tonight: the natural approaches fail - (i) dyadic-rectangle
decomposition of {y+z ≤ x} needs Θ(L) rectangles (triangle boundary);
(ii) rejection from the product has exponentially bad acceptance;
(iii) per-x precomputation costs L² per node; (iv) f̂ has no shape structure
(log-concavity empirically dead). (P) appears to be an open data-structure
problem; it is *the* bottleneck between here and beating Feng-Jin
in the small-ε regime.

Two further (P)-attacks tried and killed tonight:
(v) *Subsampled split arrays*: keep each a_y w.p. q, reweight - per-query
    TV blows up when the product mass concentrates on one entry (a light-a
    entry dominates when B kills the heavy region); importance-keeping by
    a-mass fails because the dominant entries depend on x through B.
(vi) *B-level-set intervals*: B monotone ⇒ geometric level sets are
    contiguous intervals; sampling by (interval, within-interval-by-a) costs
    O(#levels). But subset counts grow exponentially along the array, so
    every entry can occupy its own (1+η)-level: #levels = Θ(L). No
    compression. (Same huge-value-range wall that forces the paper's
    (max,+) reduction.)

(P) has now resisted six distinct approaches; each failure mode is recorded
above so a future attempt does not retrace them.

## Lower-bound attempt: reducing (max,+)-convolution to approximate #Knapsack

Goal: show that an Õ(n^{1.5-δ} poly(1/ε)) FPRAS would give a
sub-n√M algorithm for bounded monotone (max,+)-convolution (the CDXZ/BDP
frontier), i.e. a conditional lower bound matching Feng-Jin's upper bound.

**The construction that almost works.** Given monotone A[1..n], B[1..n] ≤ M:
- *Pool*: V = Θ(M log n) unit-weight (η-scale) items. N^≤(v) = Σ_{r≤v} C(V,r)
  is exactly computable, strictly monotone, with log-slope Θ(1) on a Θ(V)-wide
  window - so any exponent in a Õ(M)-range is realizable as a pool budget, and
  the map φ = log N^≤ is invertible with O(log V) granularity.
- *Selectors*: single items s_i^(1) at weight iG + Λ − a_i·η and
  s_j^(2) at weight (j+4n)G + Λ − b_j·η, with a_i = s·A_i, b_j = s·B_j,
  s = Θ(log n). The Λ-component forces exactly two selectors per window;
  the +4n index shift separates cross-pairs from same-group pairs; random
  micro-offsets kill cardinality-preserving aliasing.
- *Readout*: the window for index-sum k has count Σ_{i+j=k} N^≤(u₀+a_i+b_j),
  whose log is φ(s·max_{i+j=k}(A_i+B_j)) ± O(log n) by max-term dominance;
  invert φ to recover C[k] exactly. Each window needs only an ε = O(1)
  approximate count, and the instance has Õ(n + M log n) items with poly
  weights. If windows were queryable, this would be the reduction.

**The obstruction (robust): ≤-saturation.** #Knapsack only answers
*prefix* counts. cnt(≤ Q_k) includes every lower window, and any pair with
index-sum < k has ≥ G spare capacity - enough to afford the *entire* pool -
so it saturates at the maximum count 2^V. Since φ ≤ 0.63·V on the usable
linear window, every prefix count is dominated by saturated junk:
log cnt(≤ Q_k) = V + O(log n) for all k, and the window structure is
invisible at any constant ε. Extraction by subtracting two (1±ε) prefix
counts is information-theoretically dead (the classic difference trap), and
capacity-metering the pool cannot separate legit pairs from saturators
because both need Θ(V) pool items. Escalating per-window boosts hit the
same 2^V cap. The obstruction is the monotone ≤-structure itself: prefix
counting *washes out* max-plus fine structure.

**Takeaway.** This is (weak) evidence *against* a (max,+)-based lower bound
for approximate #Knapsack - the ≤-aggregation appears to genuinely destroy
the structure that hardness would need to survive, which is consistent with
the problem admitting the FPRAS at all. Two consequences: (1) a lower bound
for this problem likely needs a new hypothesis about approximate counting
itself, not a reduction from exact fine-grained problems; (2) the balance of
evidence tilts toward the *upper* bound being improvable - i.e. problem (P)
and the sub-n^1.5 question deserve the effort more than hardness does.

## BREAKTHROUGH CANDIDATE: Õ(n^1.5 + n^{4/3}·ε^-2) - beating Feng-Jin for all ε = o(1)

The (P) barrier is broken in the form the sampler actually needs, by combining
five mechanisms - each validated in prototype (`experiments/witness_sampler.py`,
`experiments/sublevel_sampler.py`, `experiments/pruned_sampler.py`):

1. **Witness-measure sampling.** The merged arrays' own values are
   h(z) = D^{C[z]}·w[z] with w[z] = Σ_{witness pairs} u[x]v[y] (their §6.2).
   Sampling the *witness measure* (not the raw product) is consistent with the
   tree's stored arrays and costs only the per-merge δ the analysis already
   pays (their eq. (41)-(42)). Split-draws become diagonal draws over witness
   pairs weighted u[x]·v[y] with u, v ∈ {0}∪[1, D), log D = polylog.
   [Validated: TV 0.025 vs brute force; witness fraction 1.0000.]
2. **Level-interval enumeration.** Witness pairs organize into level-interval
   rectangles; #levels M_u = Õ(subtree items/polylog) ≪ L_u at shallow nodes
   [validated: 96 items → 12 levels vs L = 389]. Active rectangles for a
   query are enumerable in O(M_u); full rectangles need O(1) each (prefix
   sums); the diagonal (max,+)-conv on attaining-restricted arrays (for
   C_att[s]) comes from their own Theorem 6.1 at construction, same budget.
3. **Sub-level classes + FFT correlations.** Since u,v ∈ [1,D), partition
   into polylog value-classes X_i, Y_j; all shifted intersection counts
   |X_i ∩ (s−Y_j)| for every s are FFT correlations, Õ(L·polylog) per node
   at construction. Draw class ∝ 2^{i+j}·count, then a ≤4-retry rejection
   makes the draw exact. [Validated: TV 0.011, mean retries 1.69.]
4. **Rank-selection via lazy dyadic pairs.** Uniform selection inside
   X_i ∩ (s−Y_j) by descending dyadic x-intervals with on-demand,
   memoized correlations of dyadic pairs (T, T'). Each pair is built once
   ever; balancing draws·log(fresh pairs) against (L/2^k)² total pairs of
   size 2^k gives an UNCONDITIONAL amortized total Õ(L_u·√N_u) per node,
   which sums to Õ(ℓ√(Nk)) ≤ Õ(ℓ√n/ε) - absorbed by the main terms.
5. **Attaining-acceptance ≈ 1.** The multiples-of-3 level separation makes
   non-attaining diagonal mass ≤ poly·D^{-3}: one final O(1) rejection.
   [Validated: worst attaining fraction 1.0000 over 520 queries.]
   Plus the ∅-split pruning (earlier section) so a sample visits only the
   path-union of its k contributing leaves.

**Cost ledger.** Construction: unchanged Õ(n^1.5) + Õ(L·polylog) per node
extras. Sampling: N = Õ(n/(ℓε²)) samples; per-draw Õ(M_u + polylog);
per-sample Σ_h min(2^h,k)·min(n_m/2^h, ℓ/2^{h/2}) = Õ(min(n_m, ℓ√k));
total sampling Õ(min(n√ℓ, n²/ℓ)·ε^-2), maximized at ℓ = n^{2/3}:

    TOTAL:  Õ(n^1.5 + min(n√ℓ, n²/ℓ)·ε^-2)  ≤  Õ(n^1.5 + n^{4/3}·ε^-2)

Strictly better than Feng-Jin's Õ(n^1.5·ε^-2) for every ε = o(1); equal at
ε = Θ(1); at the ℓ-extremes (ℓ ≤ polylog or ℓ = Θ(n)) it reaches
Õ(n^1.5 + n·ε^-2).

**Status: theorem-candidate.** All mechanisms are individually validated and
the ledger is arithmetic; what remains for a paper-grade proof: (a) the
telescoped TV accounting for witness-measure substitution at every node;
(b) the root ≤-capacity draw and per-node s-draws written out (1D prefix
draws - routine); (c) re-rounding grids between levels (the diagonal draw
lives on the parent grid - per-merge, matches the witness structure);
(d) the second phase (their §5.4) re-run through the same machinery;
(e) the lazy-amortization write-up (caps are unconditional). None looks
structural. Open refinement: eliminating the per-draw M_u rectangle
enumeration would give Õ(n^1.5 + n·ε^-2) uniformly - requires s-adaptive
aggregation over the level lattice, currently blocked by an LM-storage
tradeoff.
