/-
# Stage F.0: the exact-arrays instantiation - a complete verified core

Instantiating the whole chain with exact count arrays (kernel error zero)
yields a fully machine-checked randomized approximate-counting core:

* `samplerMassK_exact_eq` - the stored-kernel sampler with exact kernels
  IS Stage A's uniform sampler (interface check for Stage F);
* `expect1_uniform_indicator` - the meaning lemma: the estimated quantity
  is exactly `#(solutions satisfying P) / #solutions`;
* `fpras_relative` - the headline corollary: `N ≥ 1/(ε²ρ²)` samples
  estimate any indicator probability `p ≥ ρ` within relative error `ε`,
  except with probability at most `1/4`.

What remains beyond this file is only performance: the fast construction
(Feng-Jin Theorem 6.1) producing `(1±δ)`-witness arrays - consumed here
through the Stage B hypotheses - in `Õ(n^1.5)` time.
-/
import SharpKnapsack.SamplerAssembly

open Finset

/-- The exact kernels form a valid stored-kernel family. -/
theorem exactKernel_ok : KernelOK exactKernel where
  nonneg := exactKernel_nonneg
  total := exactKernel_total
  supp := fun S s y _ h => exactKernel_supp S s y h

/-- With exact kernels, the stored-kernel sampler is the uniform sampler. -/
theorem samplerMassK_exact_eq (S : List ℕ) (t : ℕ) (m : List Bool) :
    samplerMassK (exactRootKernel S t) exactKernel S t m = samplerMass S t m := by
  unfold samplerMassK samplerMass
  apply Finset.sum_congr rfl
  intro s _
  rw [splitMassK_exact]
  rfl

theorem samplerMass_nonneg' (S : List ℕ) (t : ℕ) (m : List Bool) :
    0 ≤ samplerMass S t m := by
  rw [samplerMass_spec]
  split <;> positivity

theorem samplerMass_total_finset (S : List ℕ) (t : ℕ) :
    ∑ m ∈ maskFinset S.length, samplerMass S t m = 1 := by
  rw [sum_maskFinset_eq_list]
  exact samplerMass_total S t

/-- **The meaning lemma**: under the sampler, the expectation of the
indicator of `P` is exactly the fraction of solutions satisfying `P`. -/
theorem expect1_uniform_indicator (S : List ℕ) (t : ℕ)
    (P : List Bool → Prop) [DecidablePred P] :
    expect1 (maskFinset S.length) (samplerMass S t)
        (fun m => if P m then 1 else 0) =
      (((maskFinset S.length).filter
          (fun m => maskSum m S ≤ t ∧ P m)).card : ℚ) / (countLe S t : ℚ) := by
  unfold expect1
  have h : ∀ m ∈ maskFinset S.length,
      samplerMass S t m * (if P m then 1 else 0) =
      if maskSum m S ≤ t ∧ P m then ((countLe S t : ℚ))⁻¹ else 0 := by
    intro m hm
    rw [samplerMass_spec]
    have hl := mem_maskFinset.mp hm
    by_cases hP : P m
    · by_cases hle : maskSum m S ≤ t
      · rw [if_pos ⟨hl, hle⟩, if_pos hP, if_pos ⟨hle, hP⟩, mul_one]
      · rw [if_neg (by rintro ⟨-, h2⟩; exact hle h2), if_pos hP,
          if_neg (by rintro ⟨h1, -⟩; exact hle h1), mul_one]
    · rw [if_neg hP, mul_zero, if_neg (by rintro ⟨-, h2⟩; exact hP h2)]
  rw [Finset.sum_congr rfl h, Finset.sum_ite, Finset.sum_const, Finset.sum_const]
  simp only [mul_zero, add_zero, nsmul_eq_mul]
  rw [div_eq_mul_inv]

/-- **The verified approximate-counting core**: `N` independent runs of the
sampler estimate any indicator probability `p ≥ ρ` within relative error
`ε`, except with probability at most `1/4`, provided `N·ε²·ρ² ≥ 1`. -/
theorem fpras_relative (S : List ℕ) (t : ℕ)
    (f : List Bool → ℚ) (hind : ∀ x, f x * f x = f x)
    (hf01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (ρ ε : ℚ) (hρ : 0 < ρ) (hε : 0 < ε)
    (hp : ρ ≤ expect1 (maskFinset S.length) (samplerMass S t) f)
    (N : ℕ) (hN : 0 < N) (hNbig : 1 ≤ N * (ε ^ 2 * ρ ^ 2)) :
    (∑ v ∈ (vecs (maskFinset S.length) N).filter
        (fun v => ε * expect1 (maskFinset S.length) (samplerMass S t) f ≤
          |sumStat f v / N - expect1 (maskFinset S.length) (samplerMass S t) f|),
      prodMass (samplerMass S t) v) ≤ 1 / 4 := by
  set μ := samplerMass S t with hμ
  set p := expect1 (maskFinset S.length) μ f with hpdef
  have hμnn : ∀ m, 0 ≤ μ m := fun m => samplerMass_nonneg' S t m
  have hμtot : ∑ m ∈ maskFinset S.length, μ m = 1 := samplerMass_total_finset S t
  have hsub : (vecs (maskFinset S.length) N).filter
      (fun v => ε * p ≤ |sumStat f v / N - p|) ⊆
      (vecs (maskFinset S.length) N).filter
      (fun v => ε * ρ ≤ |sumStat f v / N - p|) := by
    intro v hv
    rw [Finset.mem_filter] at hv ⊢
    refine ⟨hv.1, ?_⟩
    have h2 := hv.2
    have h3 : ε * ρ ≤ ε * p := mul_le_mul_of_nonneg_left hp (le_of_lt hε)
    linarith
  calc (∑ v ∈ (vecs (maskFinset S.length) N).filter
        (fun v => ε * p ≤ |sumStat f v / N - p|), prodMass μ v)
      ≤ ∑ v ∈ (vecs (maskFinset S.length) N).filter
        (fun v => ε * ρ ≤ |sumStat f v / N - p|), prodMass μ v :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun v _ _ => prodMass_nonneg μ hμnn v)
    _ ≤ 1 / (4 * N * (ε * ρ) ^ 2) :=
        estimator_chebyshev (maskFinset S.length) μ hμnn hμtot f hind hf01
          N hN (ε * ρ) (mul_pos hε hρ)
    _ ≤ 1 / 4 := by
        have hNQ : (0:ℚ) < (N : ℚ) := by exact_mod_cast hN
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) ?_
        calc (4:ℚ) = 4 * 1 := by ring
          _ ≤ 4 * (N * (ε ^ 2 * ρ ^ 2)) := by
              apply mul_le_mul_of_nonneg_left hNbig
              norm_num
          _ = 4 * N * (ε * ρ) ^ 2 := by ring
