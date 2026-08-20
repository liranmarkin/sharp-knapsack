/-
# Barriers for deterministic #Knapsack merges (branch `det-fptas`)

Machine-checked core of barrier B1 from
`docs/research/2026-08-20-det-fptas-notes.md`:

**Ramp hardness.** The GMW sum-approximation merge, viewed on breakpoint
sequences, asks for a min-plus convolution of monotone sequences with
UNBOUNDED values. This is as hard as general min-plus convolution:
adding the linear ramp `R·k` to both inputs (i) shifts every
anti-diagonal of the min-plus convolution by exactly `R·m` - so the
ramped instance determines the original - and (ii) makes any
`B`-bounded sequence monotone once `R ≥ 2B`. Hence the fast
bounded-monotone MinConv algorithms (values in `[n]`; e.g.
Jin-Park-Saha-Xu 2026, deterministic n^{1.5+o(1)}) cannot apply to
breakpoint merges as-is: the unbounded-value monotone case they would
need is general-MinConv-hard.
-/
import Mathlib

open Finset

/-- Min-plus convolution at anti-diagonal `m`, with the split point
ranging over `0..n` (stated for the upper half `n ≤ m`, wlog by
symmetry of the two operands). -/
def minConvAt (a b : ℕ → ℤ) (n m : ℕ) : ℤ :=
  (range (n + 1)).inf' ⟨0, mem_range.mpr (Nat.succ_pos n)⟩ (fun k => a k + b (m - k))

/-- Adding a constant commutes with `inf'`. -/
theorem inf'_add_const (s : Finset ℕ) (hs : s.Nonempty) (f : ℕ → ℤ) (c : ℤ) :
    s.inf' hs (fun k => f k + c) = s.inf' hs f + c := by
  apply le_antisymm
  · obtain ⟨k, hk, hfk⟩ := Finset.exists_mem_eq_inf' hs f
    calc s.inf' hs (fun k => f k + c) ≤ f k + c := Finset.inf'_le _ hk
      _ = s.inf' hs f + c := by rw [← hfk]
  · apply Finset.le_inf'
    intro k hk
    have h1 : s.inf' hs f ≤ f k := Finset.inf'_le _ hk
    omega

/-- **B1, part (i): the ramp shifts every anti-diagonal uniformly.**
The min-plus convolution of the ramped sequences at anti-diagonal `m`
equals the original convolution plus `R·m` - so solving the ramped
(monotone) instance solves the general one. -/
theorem ramp_minConv (a b : ℕ → ℤ) (R : ℤ) (n m : ℕ) (hm : n ≤ m) :
    minConvAt (fun k => a k + R * k) (fun l => b l + R * l) n m =
      minConvAt a b n m + R * m := by
  have hne : (range (n + 1)).Nonempty := ⟨0, mem_range.mpr (Nat.succ_pos n)⟩
  have h1 : minConvAt (fun k => a k + R * k) (fun l => b l + R * l) n m =
      (range (n + 1)).inf' hne (fun k => (a k + b (m - k)) + R * m) := by
    apply Finset.inf'_congr _ rfl
    intro k hk
    have hkn : k ≤ n := by
      have := mem_range.mp hk
      omega
    have hkm : k ≤ m := le_trans hkn hm
    have hcast : ((m - k : ℕ) : ℤ) = (m : ℤ) - (k : ℤ) := by
      push_cast [Nat.cast_sub hkm]
      ring
    calc (a k + R * k) + (b (m - k) + R * ((m - k : ℕ) : ℤ))
        = (a k + b (m - k)) + R * ((k : ℤ) + ((m - k : ℕ) : ℤ)) := by ring
      _ = (a k + b (m - k)) + R * m := by
          rw [hcast]
          ring
  rw [h1, inf'_add_const]
  rfl

/-- **B1, part (ii): the ramp makes any bounded sequence monotone.**
If `|a k| ≤ B` on `0..n` and `R ≥ 2B`, then `k ↦ a k + R·k` is
monotone non-decreasing on `0..n`. So bounded-VALUE structure is
destroyed at exactly the moment monotonicity is gained: monotone
MinConv with unbounded values contains all of MinConv. -/
theorem ramp_monotone (a : ℕ → ℤ) (B R : ℤ) (n : ℕ)
    (hB : ∀ k ≤ n, -B ≤ a k ∧ a k ≤ B) (hR : 2 * B ≤ R) :
    ∀ k, k + 1 ≤ n → a k + R * k ≤ a (k + 1) + R * (k + 1) := by
  intro k hk
  have h1 := hB k (by omega)
  have h2 := hB (k + 1) hk
  have hcast : (((k + 1 : ℕ)) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
  have hgoal : a k - a (k + 1) ≤ R := by omega
  calc a k + R * k = a (k + 1) + (a k - a (k + 1)) + R * k := by ring
    _ ≤ a (k + 1) + R + R * k := by omega
    _ = a (k + 1) + R * ((k : ℤ) + 1) := by ring
    _ = a (k + 1) + R * ((k + 1 : ℕ) : ℤ) := by rw [hcast]
