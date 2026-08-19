/-
# The Feng-Jin oracle interface (their Theorem 6.1) and the mod-3 pieces

This folder holds the results we RELY ON from Feng-Jin (SODA 2025).
This file states the interface of their Theorem 6.1 - the witness
convolution oracle - as the postcondition `WitnessOracle`, together with
their §6.2 mod-3 piece decomposition that produces the residue-separated
inputs it consumes. The fast implementation of this interface (FFT +
random primes, [FJ25, Thm 6.1] / [BDP24]) is used as published; a
verified slow implementation inhabiting the same interface lives in
`New/SamplerMerge.lean`.
-/
import Mathlib

open Finset

/-- Exact rational convolution on a diagonal. -/
def convQ (f g : ℕ → ℚ) (s : ℕ) : ℚ := ∑ y ∈ range (s + 1), f y * g (s - y)

/-- The postcondition of Feng-Jin Theorem 6.1, per position: `C` bounds all
supported level sums, is attained when the diagonal is nonempty, and the
oracle value is exactly the attaining mass. -/
def WitnessOracle (f g : ℕ → ℚ) (lv lw : ℕ → ℤ) (h : ℕ → ℚ) : Prop :=
  ∀ s, ∃ C : ℤ,
    (∀ y ∈ range (s + 1), f y * g (s - y) ≠ 0 → lv y + lw (s - y) ≤ C) ∧
    (convQ f g s ≠ 0 →
      ∃ y ∈ range (s + 1), f y * g (s - y) ≠ 0 ∧ lv y + lw (s - y) = C) ∧
    h s = ∑ y ∈ range (s + 1) with lv y + lw (s - y) = C, f y * g (s - y)

/-! ### The mod-3 piece decomposition

Real arrays have arbitrary level residues; splitting each factor by level
residue mod 3 yields nine piece-pairs, each with constant level-sum
residue on its support - exactly the `hsep3` hypothesis above. -/

/-- The level-residue-`i` piece of an array. -/
def pieceOf (lv : ℕ → ℤ) (i : ℤ) (f : ℕ → ℚ) : ℕ → ℚ :=
  fun y => if lv y % 3 = i then f y else 0

theorem pieceOf_support (lv : ℕ → ℤ) (i : ℤ) (f : ℕ → ℚ) (y : ℕ)
    (h : pieceOf lv i f y ≠ 0) : lv y % 3 = i ∧ f y ≠ 0 := by
  by_cases hi : lv y % 3 = i
  · refine ⟨hi, ?_⟩
    rw [pieceOf, if_pos hi] at h
    exact h
  · rw [pieceOf, if_neg hi] at h
    exact absurd rfl h

/-- Each piece-pair has constant level-sum residue on its support. -/
theorem pieceOf_residue (lv lw : ℕ → ℤ) (i j : ℤ) (f g : ℕ → ℚ)
    (y z : ℕ) (hy : pieceOf lv i f y ≠ 0) (hz : pieceOf lw j g z ≠ 0) :
    (lv y + lw z) % 3 = (i + j) % 3 := by
  obtain ⟨hi, -⟩ := pieceOf_support lv i f y hy
  obtain ⟨hj, -⟩ := pieceOf_support lw j g z hz
  omega

/-- The three pieces reassemble the array. -/
theorem pieceOf_sum (lv : ℕ → ℤ) (f : ℕ → ℚ) (y : ℕ) :
    pieceOf lv 0 f y + pieceOf lv 1 f y + pieceOf lv 2 f y = f y := by
  have h3 : lv y % 3 = 0 ∨ lv y % 3 = 1 ∨ lv y % 3 = 2 := by omega
  rcases h3 with h | h | h <;>
    simp [pieceOf, h]

/-- The convolution decomposes over the nine piece-pairs. -/
theorem convQ_pieces (lv lw : ℕ → ℤ) (f g : ℕ → ℚ) (s : ℕ) :
    convQ f g s =
      ∑ i ∈ range 3, ∑ j ∈ range 3,
        convQ (pieceOf lv i f) (pieceOf lw j g) s := by
  simp only [convQ]
  have hstep1 : ∀ i : ℕ, (∑ j ∈ range 3, ∑ y ∈ range (s + 1),
      pieceOf lv i f y * pieceOf lw j g (s - y)) =
      ∑ y ∈ range (s + 1), ∑ j ∈ range 3,
        pieceOf lv i f y * pieceOf lw j g (s - y) := fun i => Finset.sum_comm
  rw [Finset.sum_congr rfl (fun i _ => hstep1 i), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  have hexp : (∑ i ∈ range 3, ∑ j ∈ range 3,
      pieceOf lv i f y * pieceOf lw j g (s - y)) =
      (∑ i ∈ range 3, pieceOf lv i f y) *
        ∑ j ∈ range 3, pieceOf lw j g (s - y) := by
    rw [Finset.sum_mul_sum]
  have hfs : (∑ i ∈ range 3, pieceOf lv (i : ℤ) f y) = f y := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    push_cast
    exact pieceOf_sum lv f y
  have hgs : (∑ j ∈ range 3, pieceOf lw (j : ℤ) g (s - y)) = g (s - y) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    push_cast
    exact pieceOf_sum lw g (s - y)
  rw [hexp, hfs, hgs]
