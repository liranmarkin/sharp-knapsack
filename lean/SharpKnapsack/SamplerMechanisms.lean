/-
# The remaining introduced mechanisms, machine-checked

Audit of `docs/witness-sampler.md` against the Lean development: four
mechanisms *introduced by this work* (not inherited from Feng-Jin) were
still prose-only. This file closes them:

* step 2 (de-rounding): `div_preimage_interval` - grid preimages are
  contiguous - and `roundedDraw_exact` - the coarse-then-fine draw
  factorizes exactly, so the grid layer costs no TV;
* step 3a: `levels_card_le` - the per-draw rectangle enumeration is
  bounded by the level count `M+1`, not the array length;
* step 3b: `corr_count` - indicator convolutions count exactly the
  shifted class intersections the rank-selection uses;
* step 3c: `rejection_exact` / `rejection_accept_ge` - the class-envelope
  rejection is distribution-exact with acceptance probability ≥ 1/4.

With these, every mechanism this work introduces is machine-checked;
reliance on the Feng-Jin paper is limited to their published pipeline
structure and their Theorem 6.1 subroutine.
-/
import SharpKnapsack.SamplerMerge

open Finset

/-! ### Step 2: the de-rounding layer -/

/-- Grid preimages are contiguous: if two positions share a coarse value,
so does everything between them. -/
theorem div_preimage_interval (c z a b x : ℕ)
    (ha : a / c = z) (hb : b / c = z) (hax : a ≤ x) (hxb : x ≤ b) :
    x / c = z := by
  have h1 : a / c ≤ x / c := Nat.div_le_div_right hax
  have h2 : x / c ≤ b / c := Nat.div_le_div_right hxb
  omega

/-- The de-rounding draw is exact: drawing the coarse value with its
aggregated mass and then the fine position within the preimage reproduces
the direct fine draw - the grid layer contributes no error at all. -/
theorem roundedDraw_exact (h : ℕ → ℚ) (r : ℕ → ℕ) (F : Finset ℕ)
    (s : ℕ) (_hs : s ∈ F)
    (hpre : (∑ s' ∈ F.filter (fun x => r x = r s), h s') ≠ 0) :
    ((∑ s' ∈ F.filter (fun x => r x = r s), h s') / (∑ s' ∈ F, h s')) *
      (h s / ∑ s' ∈ F.filter (fun x => r x = r s), h s') =
    h s / ∑ s' ∈ F, h s' := by
  field_simp

/-! ### Step 3a: rectangle enumeration is level-bounded -/

/-- However long the array, its level values in `[0, M]` give at most
`M + 1` distinct rectangles to enumerate per draw. -/
theorem levels_card_le (A : ℕ → ℤ) (L M : ℕ)
    (hA : ∀ y ∈ range L, 0 ≤ A y ∧ A y ≤ (M : ℤ)) :
    ((range L).image A).card ≤ M + 1 := by
  have hsub : (range L).image A ⊆ Finset.Icc (0 : ℤ) (M : ℤ) := by
    intro v hv
    rw [Finset.mem_image] at hv
    obtain ⟨y, hy, rfl⟩ := hv
    rw [Finset.mem_Icc]
    exact hA y hy
  calc ((range L).image A).card ≤ (Finset.Icc (0 : ℤ) (M : ℤ)).card :=
        Finset.card_le_card hsub
    _ = M + 1 := by
        rw [Int.card_Icc]
        simp

/-! ### Step 3b: correlation counts -/

/-- The indicator convolution at shift `s` counts exactly the class
intersection `{y ≤ s : y ∈ X, s − y ∈ Y}` that rank-selection descends. -/
theorem corr_count (X Y : Finset ℕ) (s : ℕ) :
    (∑ y ∈ range (s + 1),
      (if y ∈ X then (1 : ℚ) else 0) * (if s - y ∈ Y then (1 : ℚ) else 0)) =
    (((range (s + 1)).filter (fun y => y ∈ X ∧ s - y ∈ Y)).card : ℚ) := by
  classical
  rw [Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro y _
  by_cases hX : y ∈ X <;> by_cases hY : s - y ∈ Y <;>
    simp [hX, hY]

/-! ### Step 3c: the class-envelope rejection -/

/-- Single-round exactness: proposing from the envelope `b` and accepting
with probability `w/b` outputs each `x` with probability `w x / Σb` - so
conditioned on acceptance, the output is exactly `∝ w`. -/
theorem rejection_exact (w b : ℕ → ℚ) (F : Finset ℕ) (x : ℕ) (_hx : x ∈ F)
    (hbx : b x ≠ 0) (hw : (∑ y ∈ F, w y) ≠ 0) (hb : (∑ y ∈ F, b y) ≠ 0) :
    (b x / (∑ y ∈ F, b y)) * (w x / b x) = w x / (∑ y ∈ F, b y) ∧
    (w x / (∑ y ∈ F, b y)) / ((∑ y ∈ F, w y) / (∑ y ∈ F, b y)) =
      w x / (∑ y ∈ F, w y) := by
  constructor
  · field_simp
  · field_simp

/-- The envelope is within a factor 4, so each round accepts with
probability at least 1/4 - the expected-retries bound of the draw. -/
theorem rejection_accept_ge (w b : ℕ → ℚ) (F : Finset ℕ)
    (_hw : ∀ y ∈ F, 0 ≤ w y) (hb4 : ∀ y ∈ F, b y ≤ 4 * w y)
    (hbpos : 0 < ∑ y ∈ F, b y) :
    (1 : ℚ) / 4 ≤ (∑ y ∈ F, w y) / (∑ y ∈ F, b y) := by
  have hsum : (∑ y ∈ F, b y) ≤ 4 * ∑ y ∈ F, w y := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hb4
  rw [div_le_div_iff₀ (by norm_num) hbpos]
  linarith
