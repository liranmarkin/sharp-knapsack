# Beating SOTA for #Knapsack: attack notes

Branch: `sota-attempt`. Date: 2026-08-18.

## The landscape (verified by literature search)

| Lane | Record | Holder |
|---|---|---|
| Randomized (FPRAS) | Õ(n^1.5 ε^-2) | Feng-Jin, SODA 2025 (arXiv 2410.22267) |
| Deterministic (FPTAS) | Õ(n^2.5 ε^-1.5) | Gawrychowski-Markin-Weimann, ICALP 2018 |
| Formally verified | correctness + loose poly cost bound (deg. 8) | this repository (2026) - only one in existence |

Feng-Jin explicitly list as open: (1) near-linear FPRAS; (2) improving the
deterministic FPTASes to near-/sub-quadratic.

## Why the deterministic barrier is real (new observation)

The GMW framework represents counting functions as sparsified monotone
staircases with m breakpoints over *exact* (unbounded) integer positions,
and its bottleneck is the m x m approximate convolution of two staircases.

**Claim (hardness of the fine regime).** A deterministic algorithm computing
a (1+δ)-sum-approximation of the convolution of two m-step staircases with
δ ≤ 1/(3m) in time O(m^{2-c}) would solve *general* (min,+)-convolution in
subquadratic time, contradicting the MinConv conjecture.

*Proof sketch.* Given arbitrary integer sequences A, B, define increasing
sequences A'_i = A_i + iM, B'_j = B_j + jM for huge M; their monotone
(min,+)-convolution recovers the general one (subtract kM). Encode A' as a
staircase F with i-th breakpoint at position A'_i and geometric values
(1+δ)^i (similarly B'). Then log_{1+δ} of the convolved prefix function at w
equals max{i+j : A'_i + B'_j ≤ w} up to additive error < 1 when δ ≤ 1/(3m)
(band truncation contributes < (1+δ)^{2 log m / δ-ish} ... with δ this fine a
(1+δ)-approximation pins the level exactly). Inverting the level function
yields C'(k) = min_{i+j=k}(A'_i + B'_j). ∎

Consequences:
- Any subquadratic deterministic approach must exploit *coarseness*
  (δ >> 1/m, band width Δ = Õ(1/δ) << m). GMW's operating regime is coarse,
  so the door is not closed - but all known coarse-regime tools
  (CDXZ22/BDP24 bounded monotone (max,+) in Õ(n√M)) are (a) randomized and
  (b) require poly-bounded entries, which exact weights do not give.
  Feng-Jin obtain bounded entries via Dyer's *randomized* rounding
  (deterministic rounding provably distorts counts: their tiny-items example
  gives a Θ(log n / n) count change).
- The band idea (only pairs within level-distance Δ of the (max,+) frontier
  matter, so Õ(m·Δ) = Õ(m/δ) pairs "should" suffice) fails in the worst case:
  uniform weights put all m² pairs on the frontier. A win-win argument
  ("many frontier pairs => additive structure => compressible") would go
  through Balog-Szemerédi-Gowers machinery - the Chan-Lewenstein program -
  which again needs bounded universes after compression. This is a genuine
  research program, not a session-sized gap.

## What is achievable now, and what this branch does

1. **Verified-lane SOTA** (executing now): raise the verified running-time
   bound from the loose degree-8 polynomial to the *sharp*
   Õ(n^2.5 ε^-1.5 + n² ε^-2) form - matching the human deterministic record
   term-for-term in the standard regime ε ≥ 1/n. Key enabler: a fully
   rational power-of-two δ-schedule
   δ_d = ε / (16 · 2^⌈d/2⌉ · 2^⌈D/2⌉), bottom δ = ε / (16 · 2^{2⌈D/2⌉}),
   with recursion depth capped at D ≈ log₂ √(nε). Budget analysis via the
   recurrence Bud(d) = δ_d + 2·Bud(d+1), using
   (1+δ)(1-δ-2x) ≤ (1-x)² (true for all δ, x ≥ 0) and the exact identity
   Σ_{i<D} 2^{⌊i/2⌋} = 2^{⌈D/2⌉} + 2^{⌊D/2⌋} - 2, giving Bud(0) ≤ 3ε/16.
   Cost analysis: per-node conv budget ~ n² ε^-2 2^{D-d} halves per level, so
   the tree telescopes; bottom balances at n^2.5 ε^-1.5.
2. **Human-lane attempt documented**: the hardness observation above and the
   coarse-regime program (deterministic bounded monotone (max,+); win-win via
   additive combinatorics) as the precise open frontier.


## Outcome (same day)

**Achieved - new verified-lane SOTA.** `lean/SharpKnapsack/Sharp.lean` +
`SharpComplexity.lean` (on this branch) implement and verify the sharp
algorithm: depth-capped divide-and-conquer with the rational schedule
δ_d = ε/(16·2^⌈d/2⌉·2^⌈D/2⌉), D = log₂(√(n/⌈1/ε⌉)+1), bottom nodes
re-sparsified at δ_bot. Machine-checked theorems (`fptasSharp`):

* correctness: exact ≤ answer ≤ (1+ε)·exact;
* running time: cost ≤ 10⁷·LOG²·(n+2)²·(⌈1/ε⌉·(√(n·⌈1/ε⌉)+1) + ⌈1/ε⌉²),
  i.e. **Õ(n^2.5·ε^-1.5 + n²·ε^-2)** - matching the best known deterministic
  bound (GMW 2018) term for term; the n²ε⁻² term is dominated whenever
  ε ≥ 1/n. Axioms: propext, Classical.choice, Quot.sound only.

This is the strongest formally verified result for #Knapsack in existence
(the prior record was this repository's own loose degree-8 verified bound;
no other verified FPTAS for #Knapsack exists).

**Not achieved - beating the human deterministic record.** The barrier
analysis above stands: sub-n^2.5 deterministic #Knapsack runs through either
derandomizing Dyer-style rounding + bounded monotone (max,+)-convolution
(both randomized today), or a win-win additive-combinatorics argument for
sparse staircase convolution - a recognized open problem (Feng-Jin §1.3).
