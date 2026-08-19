/-
# The arrays-to-kernels bridge: Stage F's interface

Stage B consumes abstract kernels; the construction produces *arrays*.
This file closes the gap: any array family `F` that is pointwise within
`(1±δ)` of the exact counts, together with witness sets `Wsel` carrying
all but a `γ`-fraction of each diagonal (exactly what Stage 0's
`diagonal_witness_domination` provides), induces kernels that

* satisfy `KernelOK` (`arrayKernel_ok`), and
* are within local L1 distance `12δ + 3γ` of the exact kernels
  (`arrayKernel_close`), the `η` fed to `splitMassK_l1`/`fpras_assembly`.

After this file, verifying the fast construction (Stage F.1) reduces to:
produce arrays satisfying `ArraysOK` in `Õ(n^1.5)` time.
-/
import SharpKnapsack.New.SamplerInstance

open Finset

/-- The exact diagonal products at a node, as rationals. -/
def diagProd (S : List ℕ) (s y : ℕ) : ℚ :=
  ((count (S.take (S.length / 2)) y : ℕ) : ℚ) *
    ((count (S.drop (S.length / 2)) (s - y) : ℕ) : ℚ)

/-- The stored diagonal products. -/
def storedDiag (F : List ℕ → ℕ → ℚ) (S : List ℕ) (s y : ℕ) : ℚ :=
  F (S.take (S.length / 2)) y * F (S.drop (S.length / 2)) (s - y)

/-- The kernel the algorithm actually draws from: stored diagonal products
restricted to the witness set, normalized. -/
def arrayKernel (F : List ℕ → ℕ → ℚ) (Wsel : List ℕ → ℕ → Finset ℕ)
    (S : List ℕ) (s y : ℕ) : ℚ :=
  (if y ∈ Wsel S s then storedDiag F S s y else 0) /
    (∑ z ∈ range (s + 1), if z ∈ Wsel S s then storedDiag F S s z else 0)

/-- The stored-array specification the fast construction must meet. -/
structure ArraysOK (F : List ℕ → ℕ → ℚ) (Wsel : List ℕ → ℕ → Finset ℕ)
    (δ γ : ℚ) : Prop where
  lo : ∀ S s, (1 - δ) * ((count S s : ℕ) : ℚ) ≤ F S s
  hi : ∀ S s, F S s ≤ (1 + δ) * ((count S s : ℕ) : ℚ)
  wsub : ∀ S s, Wsel S s ⊆ range (s + 1)
  wdrop : ∀ S s, (∑ y ∈ range (s + 1) \ Wsel S s, diagProd S s y) ≤
    γ * ∑ y ∈ range (s + 1), diagProd S s y

namespace ArraysOK

variable {F : List ℕ → ℕ → ℚ} {Wsel : List ℕ → ℕ → Finset ℕ} {δ γ : ℚ}

theorem nonneg (hA : ArraysOK F Wsel δ γ) (hδ : δ ≤ 1) (S : List ℕ) (s : ℕ) :
    0 ≤ F S s := by
  have h := hA.lo S s
  have hc : (0:ℚ) ≤ ((count S s : ℕ) : ℚ) := by positivity
  nlinarith

theorem faithful (hA : ArraysOK F Wsel δ γ) (hδ : δ ≤ 1) (S : List ℕ) (s : ℕ)
    (h : F S s ≠ 0) : count S s ≠ 0 := by
  intro h0
  apply h
  have hhi := hA.hi S s
  have hlo := hA.nonneg hδ S s
  rw [h0] at hhi
  simp at hhi
  linarith

end ArraysOK

/-- The exact kernel in diagonal form. -/
theorem exactKernel_eq_diag (S : List ℕ) (s y : ℕ) :
    exactKernel S s y = diagProd S s y / ((count S s : ℕ) : ℚ) := by
  unfold exactKernel diagProd
  push_cast
  ring_nf

/-- The exact diagonal totals to the exact count (Lemma 10, again). -/
theorem diagProd_total (S : List ℕ) (s : ℕ) :
    (∑ y ∈ range (s + 1), diagProd S s y) = ((count S s : ℕ) : ℚ) := by
  have hconv : count S s =
      ∑ y ∈ range (s + 1),
        count (S.take (S.length / 2)) y * count (S.drop (S.length / 2)) (s - y) := by
    conv_lhs => rw [← List.take_append_drop (S.length / 2) S]
    rw [count_append]
    rfl
  unfold diagProd
  rw [hconv]
  push_cast
  ring

/-- The stored diagonal is within `(1 ± 3δ)` of the exact diagonal. -/
theorem storedDiag_sandwich (hA : ArraysOK F Wsel δ γ) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1)
    (S : List ℕ) (s y : ℕ) :
    (1 - 3 * δ) * diagProd S s y ≤ storedDiag F S s y ∧
      storedDiag F S s y ≤ (1 + 3 * δ) * diagProd S s y := by
  set L := S.take (S.length / 2)
  set R := S.drop (S.length / 2)
  have hcL : (0:ℚ) ≤ ((count L y : ℕ) : ℚ) := by positivity
  have hcR : (0:ℚ) ≤ ((count R (s - y) : ℕ) : ℚ) := by positivity
  have hloL := hA.lo L y
  have hhiL := hA.hi L y
  have hloR := hA.lo R (s - y)
  have hhiR := hA.hi R (s - y)
  have hFL := hA.nonneg hδ L y
  have hFR := hA.nonneg hδ R (s - y)
  have hprod : (0:ℚ) ≤ ((count L y : ℕ) : ℚ) * ((count R (s - y) : ℕ) : ℚ) :=
    mul_nonneg hcL hcR
  constructor
  · show (1 - 3 * δ) * (((count L y : ℕ) : ℚ) * ((count R (s - y) : ℕ) : ℚ)) ≤
      F L y * F R (s - y)
    have h1 : ((1 - δ) * ((count L y : ℕ) : ℚ)) *
        ((1 - δ) * ((count R (s - y) : ℕ) : ℚ)) ≤ F L y * F R (s - y) :=
      mul_le_mul hloL hloR (mul_nonneg (by linarith) hcR) hFL
    nlinarith [h1, hprod, mul_nonneg hδ0 hprod,
      mul_nonneg (mul_nonneg hδ0 hδ0) hprod]
  · show F L y * F R (s - y) ≤
      (1 + 3 * δ) * (((count L y : ℕ) : ℚ) * ((count R (s - y) : ℕ) : ℚ))
    have h2 : F L y * F R (s - y) ≤
        ((1 + δ) * ((count L y : ℕ) : ℚ)) *
          ((1 + δ) * ((count R (s - y) : ℕ) : ℚ)) :=
      mul_le_mul hhiL hhiR hFR (mul_nonneg (by linarith) hcL)
    nlinarith [h2, hprod,
      mul_nonneg (mul_nonneg hδ0 (by linarith : (0:ℚ) ≤ 1 - δ)) hprod]

/-- **The bridge, part 1**: spec-compliant arrays induce a valid kernel
family. -/
theorem arrayKernel_ok (hA : ArraysOK F Wsel δ γ)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 12) (_hγ0 : 0 ≤ γ) (hγ : γ ≤ 1 / 4) :
    KernelOK (arrayKernel F Wsel) := by
  have hδ1 : δ ≤ 1 := by linarith
  constructor
  · -- nonneg
    intro S s y
    unfold arrayKernel
    apply div_nonneg
    · split
      · exact mul_nonneg (hA.nonneg hδ1 _ _) (hA.nonneg hδ1 _ _)
      · exact le_refl 0
    · apply Finset.sum_nonneg
      intro z _
      split
      · exact mul_nonneg (hA.nonneg hδ1 _ _) (hA.nonneg hδ1 _ _)
      · exact le_refl 0
  · -- total
    intro S s hc
    unfold arrayKernel
    rw [← Finset.sum_div]
    have hRpos : 0 < ∑ z ∈ range (s + 1),
        if z ∈ Wsel S s then storedDiag F S s z else 0 := by
      have hB : (0:ℚ) < ∑ y ∈ range (s + 1), diagProd S s y := by
        rw [diagProd_total]
        have : 0 < count S s := Nat.pos_of_ne_zero hc
        exact_mod_cast this
      have hWB : (1 - γ) * (∑ y ∈ range (s + 1), diagProd S s y) ≤
          ∑ y ∈ Wsel S s, diagProd S s y := by
        have hsd := Finset.sum_sdiff (f := fun y => diagProd S s y) (hA.wsub S s)
        have hd := hA.wdrop S s
        nlinarith
      have hsel : (∑ z ∈ range (s + 1),
          if z ∈ Wsel S s then storedDiag F S s z else 0) =
          ∑ z ∈ Wsel S s, storedDiag F S s z := by
        rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr (hA.wsub S s)]
      rw [hsel]
      have hlow : (1 - 3 * δ) * (∑ z ∈ Wsel S s, diagProd S s z) ≤
          ∑ z ∈ Wsel S s, storedDiag F S s z := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun z _ =>
          (storedDiag_sandwich hA hδ0 hδ1 S s z).1
      have hWpos : (0:ℚ) < ∑ y ∈ Wsel S s, diagProd S s y := by nlinarith
      nlinarith
    exact div_self (ne_of_gt hRpos) ▸ (by rw [div_self (ne_of_gt hRpos)])
  · -- support-faithfulness
    intro S s y _ h
    unfold arrayKernel at h
    have hnum : (if y ∈ Wsel S s then storedDiag F S s y else 0) ≠ 0 := by
      intro h0
      apply h
      rw [h0, zero_div]
    have hsd : storedDiag F S s y ≠ 0 := by
      by_cases hw : y ∈ Wsel S s
      · rwa [if_pos hw] at hnum
      · rw [if_neg hw] at hnum
        exact absurd rfl hnum
    unfold storedDiag at hsd
    have h1 : F (S.take (S.length / 2)) y ≠ 0 := fun h0 => hsd (by rw [h0, zero_mul])
    have h2 : F (S.drop (S.length / 2)) (s - y) ≠ 0 := fun h0 => hsd (by rw [h0, mul_zero])
    have hδ1 : δ ≤ 1 := by linarith
    exact ⟨hA.faithful hδ1 _ _ h1, hA.faithful hδ1 _ _ h2⟩

/-- **The bridge, part 2**: the induced kernel is within local L1 distance
`12δ + 3γ` of the exact kernel - the `η` of the damage-control theorem. -/
theorem arrayKernel_close (hA : ArraysOK F Wsel δ γ)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 12) (hγ0 : 0 ≤ γ) (hγ : γ ≤ 1 / 4)
    (S : List ℕ) (s : ℕ) (hc : count S s ≠ 0) :
    (∑ y ∈ range (s + 1), |arrayKernel F Wsel S s y - exactKernel S s y|) ≤
      12 * δ + 3 * γ := by
  have hδ1 : δ ≤ 1 := by linarith
  have hmain := kernel_l1_of_approx (s + 1) (diagProd S s)
    (fun y => if y ∈ Wsel S s then storedDiag F S s y else 0)
    (Wsel S s) (hA.wsub S s) (3 * δ) γ
    (by linarith) (by linarith) hγ0 hγ
    (fun y _ => by unfold diagProd; positivity)
    (fun y _ hy => by rw [if_neg hy])
    (fun y hy => by
      rw [if_pos hy]
      exact (storedDiag_sandwich hA hδ0 hδ1 S s y).1)
    (fun y hy => by
      rw [if_pos hy]
      exact (storedDiag_sandwich hA hδ0 hδ1 S s y).2)
    (hA.wdrop S s)
    (by
      rw [diagProd_total]
      have : 0 < count S s := Nat.pos_of_ne_zero hc
      exact_mod_cast this)
  have heq : ∀ y ∈ range (s + 1),
      |(if y ∈ Wsel S s then storedDiag F S s y else 0) /
          (∑ z ∈ range (s + 1), if z ∈ Wsel S s then storedDiag F S s z else 0) -
        diagProd S s y / (∑ z ∈ range (s + 1), diagProd S s z)| =
      |arrayKernel F Wsel S s y - exactKernel S s y| := by
    intro y _
    rw [exactKernel_eq_diag, diagProd_total]
    rfl
  calc (∑ y ∈ range (s + 1), |arrayKernel F Wsel S s y - exactKernel S s y|)
      = ∑ y ∈ range (s + 1),
        |(if y ∈ Wsel S s then storedDiag F S s y else 0) /
            (∑ z ∈ range (s + 1), if z ∈ Wsel S s then storedDiag F S s z else 0) -
          diagProd S s y / (∑ z ∈ range (s + 1), diagProd S s z)| :=
        (Finset.sum_congr rfl heq).symm
    _ ≤ 4 * (3 * δ) + 3 * γ := hmain
    _ = 12 * δ + 3 * γ := by ring

/-- **The pipeline is inhabited**: the exact (executable) count arrays
meet the stored-array spec with `δ = γ = 0`. Any faster construction
replaces this instance without touching anything downstream. -/
theorem exactArraysOK :
    ArraysOK (fun S s => ((count S s : ℕ) : ℚ)) (fun _ s => range (s + 1)) 0 0 where
  lo := fun S s => by norm_num
  hi := fun S s => by norm_num
  wsub := fun S s => Finset.Subset.refl _
  wdrop := fun S s => by
    rw [Finset.sdiff_self]
    simp
