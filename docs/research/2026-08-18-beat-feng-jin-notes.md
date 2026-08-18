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

`scratchpad/probe_logconcave.py`: computed the exact subset-count-by-weight
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
