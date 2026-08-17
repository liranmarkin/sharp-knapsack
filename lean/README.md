# Formal Verification in Lean 4

A **machine-checked implementation of the main algorithm** of
"A Faster FPTAS for #Knapsack" ([`../faster-fptas-knapsack.pdf`](../faster-fptas-knapsack.pdf)):
the algorithm is written as an executable Lean function, and Lean verifies a
proof that its output is always within the promised (1+ε) factor of the true
answer.

## The problem

Given a set W = {w1, ..., wn} of non-negative integer weights and an integer
capacity C, the #Knapsack problem asks for the number of distinct subsets of W
with total weight at most C. It is the counting version of the classical
Knapsack problem and is #P-hard, yet it admits a deterministic approximation
scheme - a rarity among #P-hard counting problems. The paper gives the fastest
known deterministic FPTAS, running in O(n^2.5 eps^-1.5 log(n eps^-1) log(n eps))
time: instead of inserting items one at a time as all previous algorithms do,
it recurses on the two halves of the item list and merges the results with a
convolution of "sum approximations".

## What is verified

The correctness half of the paper's Theorem 1, end to end, for the actual
executable algorithm. The final statement (`SharpKnapsack/DivideConquer.lean`):

```lean
theorem approxCount_spec (S : List ℕ) (C : ℕ) (ε : ℚ) (h0 : 0 < ε) (h1 : ε ≤ 1) :
    countLe S C ≤ approxCount S C ε ∧
      (approxCount S C ε : ℚ) ≤ (1 + ε) * countLe S C
```

Here `approxCount S C ε` is the divide-and-conquer algorithm of the paper's
Section 4 (an ordinary, executable Lean function - it is what the CLI below
runs), and `countLe S C` is the *specification*: the number of sublists of `S`
with sum at most `C`, defined by literally enumerating all 2^n sublists:

```lean
def count (S : List ℕ) (x : ℕ) : ℕ :=
  (S.sublists'.filter fun t => decide (t.sum = x)).length

def countLe (S : List ℕ) (C : ℕ) : ℕ := prefixLe (count S) C
```

So the theorem a reader must trust reads: *the fast algorithm's answer is
sandwiched between the brute-force count and (1+ε) times it.* The proof is
`sorry`-free and depends only on Lean's three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`); no `native_decide`.

Also verified along the way, mirroring the paper:

| Lean file | Contents | Paper |
|---|---|---|
| `SharpKnapsack/Approx.lean` | prefix sums `f^≤`, shift `f\|_w`, convolution `f*g`, (1+ε)-sum approximations, and the four operations on them | Sec. 2, Defs. 3-5, Lemma 6 |
| `SharpKnapsack/Count.lean` | the counting function `k_S` and its two structural identities: insertion (`k_{S∪{w}} = k_S + k_S\|_w`) and split (`k_{S∪T} = k_S * k_T`) | Lemmas 9, 10 |
| `SharpKnapsack/Sparse.lean` | sparse representation of functions as sorted (position, value) lists; verified summation, shifting, convolution, query | Def. 7, Sec. 2 |
| `SharpKnapsack/Sparsify.lean` | the sparsification scan and its guarantee - the heart of the method | Algorithm 1, Lemma 8 |
| `SharpKnapsack/Halman.lean` | the O(n³ε⁻¹)-style insertion algorithm, verified end to end | Sec. 3 |
| `SharpKnapsack/DivideConquer.lean` | the divide-and-conquer algorithm, the depth-decaying budget analysis, and Theorem 1 | Sec. 4 |
| `SharpKnapsack/Tests.lean` | build-time differential tests against the brute-force count | - |

Approximation factors are handled multiplicatively (`K = 1+ε` throughout), so
composing approximations is literally multiplying rationals.

## Deviations from the paper

The algorithms are structurally identical to the paper's; two numeric
schedules were changed to keep all arithmetic in ℚ (the paper's constants are
irrational, and its budget analysis runs through real exponentials):

* **Section 3** per-item sparsification uses δ = ε/(2n) instead of
  (1+ε)^(1/n) − 1, justified by the Bernoulli-style bound
  (1+δ)^n (1 − nδ) ≤ 1.
* **Section 4** per-depth sparsification uses the geometric schedule
  δ(d) = (ε/20)(2/5)^d instead of ε^¾/(2c·2^(d/2)·n^¼). Writing
  Φ(d) = 1/(1 − 5δ(d)), the identity 5δ(d+1) = 2δ(d) gives the one-step
  inequality (1+δ(d))·Φ(d+1)² ≤ Φ(d), which replaces the paper's global
  product estimate; Φ(0) = 1/(1 − ε/4) ≤ 1+ε.

The paper's ratio 2^(−1/2) is tuned for the O(n^2.5) *running-time* bound,
which is out of scope here: complexity is not formally verified (the paper's
analysis stands on its own), only correctness. The heap-based streaming
convolution of Section 2 is likewise replaced by a simple sorted merge with
the same output.

## Building

Requires [elan](https://github.com/leanprover/elan) (the Lean toolchain
manager). Pinned to Lean 4.33.0 / mathlib v4.33.0.

```sh
lake exe cache get   # download prebuilt mathlib (several GB, one-time)
lake build           # builds all proofs + tests + CLI; zero sorries
```

`lake build` re-checks every proof and runs the differential tests in
`Tests.lean` (they are `#guard`s: the build fails if any algorithm output
leaves the proven interval on the test instances).

## Running

```sh
$ lake exe sharpknapsack 1/10 15 3 1 4 1 5 9 2 6
items: 8, capacity: 15, ε = 1/10
approximate #subsets with weight ≤ 15: 128
exact (brute force, for comparison):   128
```

Arguments: ε (a rational in (0,1], e.g. `1/10`), the capacity, then the
weights. For n ≤ 15 the CLI also prints the exact count. The implementation
uses exact rational/integer arithmetic and is meant as a verified reference,
not a speed record.

## Scope and next steps

- Verified: Theorem 1 (standard #Knapsack), correctness.
- Not verified: the running-time and space bounds; Theorem 2 (the integer /
  multiset version) - a natural follow-up on top of the same framework.

Design notes for the formalization live in
[`../docs/superpowers/specs/2026-08-17-lean-verification-design.md`](../docs/superpowers/specs/2026-08-17-lean-verification-design.md).
