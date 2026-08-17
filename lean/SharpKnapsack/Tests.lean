/-
# Executable differential tests

Everything here is checked at build time by `#guard`: each line evaluates the
algorithms on concrete instances and compares against the brute-force count
(`countLe` literally enumerates all `2^n` sublists). The proofs already
guarantee these properties for *all* inputs; running them on real data
additionally exercises the compiled code paths end-to-end.
-/

import SharpKnapsack.DivideConquer

open SparseFun

/-- Check `exact ≤ approx ≤ (1+ε)·exact` for every capacity below `upTo`. -/
def checkDC (S : List ℕ) (ε : ℚ) (upTo : ℕ) : Bool :=
  (List.range upTo).all fun C =>
    let exact := countLe S C
    let approx := approxCount S C ε
    decide (exact ≤ approx) && decide ((approx : ℚ) ≤ (1 + ε) * exact)

/-- The same check for the Section 3 algorithm. -/
def checkHalman (S : List ℕ) (ε : ℚ) (upTo : ℕ) : Bool :=
  (List.range upTo).all fun C =>
    let exact := countLe S C
    let approx := queryLe (halman S ε) C
    decide (exact ≤ approx) && decide ((approx : ℚ) ≤ (1 + ε) * exact)

-- The Section 3 algorithm.
#guard checkHalman [3, 1, 4, 1, 5, 9, 2, 6] (1/2) 40
#guard checkHalman [3, 1, 4, 1, 5, 9, 2, 6] (1/100) 40
#guard checkHalman (List.replicate 10 7) (1/5) 75
#guard checkHalman [] (1/2) 5
#guard checkHalman [0, 0, 3] (1/2) 10

-- The divide-and-conquer algorithm (Theorem 1).
#guard checkDC [3, 1, 4, 1, 5, 9, 2, 6, 5, 3] (1/2) 45
#guard checkDC [3, 1, 4, 1, 5, 9, 2, 6, 5, 3] (1/100) 45
#guard checkDC (List.replicate 12 5) (1/3) 65
#guard checkDC [100, 1, 50, 2, 25, 4, 12, 8] (1/2) 210
#guard checkDC [] (1/2) 5
#guard checkDC [0, 0, 7] 1 15

-- Sparsification compresses: 100 unit points at δ = 1/2 fit in ≤ 15 points.
#guard (sparsify (1/2) ((List.range 100).map fun i => (i, 1))).length ≤ 15

-- Sparsification with δ = 0 is exact on prefix sums.
#guard
  let L : SparseFun := (List.range 60).map fun i => (i, i + 1)
  (List.range 70).all fun x => queryLe (sparsify 0 L) x == queryLe L x
