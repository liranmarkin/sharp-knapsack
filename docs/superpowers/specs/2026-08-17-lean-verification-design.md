# Formal Verification of "A Faster FPTAS for #Knapsack" in Lean 4

**Date:** 2026-08-17
**Paper:** Gawrychowski, Markin, Weimann. *A Faster FPTAS for #Knapsack*, ICALP 2018 (`faster-fptas-knapsack.pdf`).
**Goal:** An executable Lean 4 implementation of the paper's divide-and-conquer FPTAS (Theorem 1) with a machine-checked proof that its output approximates the true #Knapsack count within a factor of (1+eps). The Lean function doubles as the reference implementation.

## Scope

- Theorem 1 only (standard #Knapsack, subsets). The integer/multiset version (Theorem 2) is out of scope.
- Correctness only. Running-time and space bounds are stated in the paper but not formally verified; the implementation follows the paper's algorithmic structure so its practical performance is polynomial.
- Toolchain: Lean 4 + mathlib (pinned stable release), built with lake. Acceptance: `lake build` succeeds with zero `sorry`.

## Architecture

Two layers, mirroring the paper:

### Abstract layer (the math, Sections 2-3 of the paper)

Functions are plain `f : ℕ → ℕ`.

- `count (S : List ℕ) (x : ℕ) : ℕ` - number of sublists of `S` summing to exactly `x` (the paper's k_S). `countLe S C` is the #Knapsack answer k_S^≤(C).
- `prefixLe f x = ∑ y ≤ x, f y` - the paper's f^≤.
- `shiftFun w f` and `convFun f g` - the paper's shift f|_w and convolution f*g.
- Approximation is multiplicative, parametrized by a factor `K : ℚ` (K ≥ 1) rather than by eps, so composition is clean multiplication:
  - `IsApprox K F f := ∀ x, f x ≤ F x ∧ (F x : ℚ) ≤ K * f x`
  - `IsSumApprox K F f := IsApprox K (prefixLe F) (prefixLe f)` (paper Def. 5, with K = 1+eps).
- Paper Lemma 6 becomes four lemmas: composition multiplies factors; pointwise sum, shift, and convolution preserve/multiply factors.
- Paper Lemma 9: `count (w :: S) = count S + shiftFun w (count S)`.
- Paper Lemma 10: `count (A ++ B) = convFun (count A) (count B)`.

### Concrete layer (the executable, Section 2's representations)

- `SparseFun := List (ℕ × ℕ)` - sorted (position, value) pairs, values positive (paper Def. 7), with a well-formedness predicate and a denotation `⟦·⟧ : SparseFun → (ℕ → ℕ)`.
- Executable operations `add`, `shift`, `conv`, `sparsify δ` (paper Algorithm 1), `queryLe`, each with a spec lemma connecting it to the abstract layer. The key one is Lemma 8: `⟦sparsify δ F⟧` is a (1+δ)-sum approximation of `⟦F⟧`.
- Exact arithmetic only: ℕ values, ℚ thresholds. The paper's heap-based streaming convolution is replaced by a simple sorted merge (same output, no verified complexity claim).

## The algorithms

### Phase A - simplified Halman (paper Section 3)

`halman (S : List ℕ) (ε : ℚ) : SparseFun` - insert items one at a time; after each insertion sparsify with per-item δ = ε/(2n).

**Deviation from the paper:** the paper's per-step δ = (1+ε)^(1/n) − 1 is irrational. We use δ = ε/(2n) and prove in ℚ, via the Bernoulli-style bound (1+δ)^n ≤ 1/(1−nδ), that the accumulated factor is ≤ 1+ε for ε ∈ (0,1]. Same algorithm shape, rational arithmetic, machine-checkable.

Theorem: for 0 < ε ≤ 1, `⟦halman S ε⟧` is a (1+ε)-sum approximation of `count S`.

### Phase B - divide and conquer (paper Section 4, the main result)

`dc (S : List ℕ) (d : ℕ) : SparseFun` at recursion depth d:
- if `|S| ≤ T` (threshold `T = max 1 (Nat.sqrt n)`), run the Halman loop on S with overall target δ(d);
- else split S in the middle, recurse on both halves at depth d+1, combine with `sparsify (δ d) (conv (dc A (d+1)) (dc B (d+1)))`.

**Deviation from the paper:** the paper's depth schedule δ_i = ε^(3/4)/(2c·2^(i/2)·n^(1/4)) involves irrational powers, and its budget analysis uses real exponentials. We use the geometric schedule

  δ(d) = (ε/20)·(2/5)^d.

Any ratio x < 1/2 admits a one-line budget induction: with K = 1/(1−2x) = 5, the total approximation factor Φ(S, d) satisfies Φ ≤ 1/(1 − K·δ(d)) by structural induction over the recursion tree, giving Φ(S, 0) ≤ 1/(1 − ε/4) ≤ 1+ε. The algorithm's structure - middle recursion, convolution merge, geometrically-decaying per-depth sparsification - is exactly the paper's; only the constants differ (the paper's 2^(−i/2) ratio is tuned for the O(n^2.5) time bound, which we do not verify).

Main theorem (Theorem 1, correctness part): for 0 < ε ≤ 1 and any capacity C,

  `countLe S C ≤ answer` and `answer ≤ (1+ε) · countLe S C`

where `answer = queryLe (dc S 0) C`.

## Module map

| File | Contents | Paper |
|---|---|---|
| `SharpKnapsack/Approx.lean` | prefixLe, shiftFun, convFun, IsApprox, IsSumApprox, Lemma 6 | Sec. 2 |
| `SharpKnapsack/Count.lean` | count, countLe, Lemmas 9 & 10 | Sec. 3-4 |
| `SharpKnapsack/Sparse.lean` | SparseFun, WF, ⟦·⟧, add/shift/conv/queryLe + specs | Def. 7 |
| `SharpKnapsack/Sparsify.lean` | sparsify + Lemma 8 | Alg. 1, Lemma 8 |
| `SharpKnapsack/Halman.lean` | halman + correctness | Sec. 3 |
| `SharpKnapsack/DivideConquer.lean` | dc + budget induction + main theorem | Sec. 4 |
| `SharpKnapsack/Tests.lean` | brute-force cross-checks (`decide`/`#eval`) | - |
| `Main.lean` | CLI: reads weights, capacity, eps; prints the approximate count | - |

## Testing and observability

- `count`/`countLe` are directly executable (exponential brute force) and serve as the trusted reference for differential tests on small instances.
- A test file asserts `halman` and `dc` outputs lie in the proven interval on a battery of small fixed instances - redundant with the proof, but exercises the executable path end-to-end.
- CLI target `lake exe sharpknapsack` for manual runs; errors (bad input) reported with explicit messages.

## Milestones

Each milestone builds green (`lake build`, no sorry) and is committed.

1. Package skeleton + Approx + Count (abstract layer complete).
2. Sparse layer with op specs.
3. Sparsify + Lemma 8 (hardest single proof).
4. Halman verified end-to-end - first complete verified FPTAS for #Knapsack.
5. Divide-and-conquer + budget + main theorem (the paper's Theorem 1).
6. Tests, CLI, README update explaining the development for human readers.
