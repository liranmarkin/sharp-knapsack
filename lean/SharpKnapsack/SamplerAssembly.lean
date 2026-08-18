/-
# The assembly theorem: Stages A + B + C composed

The top-level guarantee of the sampling half of the FPRAS, machine-checked
end to end: run the *stored-kernel* sampler (Stage B) `N` times
independently (Stage C) and average an indicator; then, except with
Chebyshev probability `1/(4Na²)`, the empirical mean is within
`a + Δ` of the indicator's expectation under the *exactly uniform*
distribution over knapsack solutions (Stage A), where
`Δ = η₀ + η · #internal nodes` is the accumulated kernel error.

`fpras_assembly` is the statement the algorithm's ε-guarantee instantiates:
Stage D's bounds choose `N`, `a`, and the indicator so that `a + Δ` is an
`ε`-fraction of the estimated ratio.
-/
import SharpKnapsack.SamplerEstimator

open Finset

/-- Totality of the full stored-kernel sampler. -/
theorem samplerMassK_total (Q₀ : ℕ → ℚ) (Q : List ℕ → ℕ → ℕ → ℚ)
    (hQ : KernelOK Q) (S : List ℕ) (t : ℕ)
    (hQ₀tot : ∑ s ∈ range (t + 1), Q₀ s = 1)
    (hQ₀supp : ∀ s, s ≤ t → Q₀ s ≠ 0 → count S s ≠ 0) :
    ∑ m ∈ maskFinset S.length, samplerMassK Q₀ Q S t m = 1 := by
  unfold samplerMassK
  rw [Finset.sum_comm]
  have h : ∀ s ∈ range (t + 1),
      (∑ m ∈ maskFinset S.length, Q₀ s * splitMassK Q S s m) = Q₀ s := by
    intro s hs
    rw [Finset.mem_range] at hs
    rw [← Finset.mul_sum]
    by_cases hq : Q₀ s = 0
    · rw [hq, zero_mul]
    · rw [splitMassK_total Q hQ S s (hQ₀supp s (by omega) hq), mul_one]
  rw [Finset.sum_congr rfl h]
  exact hQ₀tot

/-- Expectations move by at most the L1 distance, for `[0,1]`-valued
statistics. -/
theorem expect1_l1 (Ωf : Finset (List Bool)) (μ μ' : List Bool → ℚ)
    (f : List Bool → ℚ) (hf01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    |expect1 Ωf μ' f - expect1 Ωf μ f| ≤ ∑ m ∈ Ωf, |μ' m - μ m| := by
  unfold expect1
  rw [← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum ?_)
  intro m _
  have h : μ' m * f m - μ m * f m = (μ' m - μ m) * f m := by ring
  rw [h, abs_mul]
  calc |μ' m - μ m| * |f m| ≤ |μ' m - μ m| * 1 := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        rw [abs_of_nonneg (hf01 m).1]
        exact (hf01 m).2
    _ = |μ' m - μ m| := mul_one _

/-- **The assembly theorem.** Under the stored-kernel sampler's `N`-fold
product run, the empirical mean of an indicator deviates from its
expectation under the EXACT uniform solution distribution by more than
`a + (η₀ + η·#internal nodes)` with probability at most `1/(4Na²)`. -/
theorem fpras_assembly (S : List ℕ) (t : ℕ)
    (Q₀ : ℕ → ℚ) (Q : List ℕ → ℕ → ℕ → ℚ) (hQ : KernelOK Q)
    (η₀ η : ℚ)
    (hQ₀nn : ∀ s, 0 ≤ Q₀ s)
    (hQ₀tot : ∑ s ∈ range (t + 1), Q₀ s = 1)
    (hQ₀supp : ∀ s, s ≤ t → Q₀ s ≠ 0 → count S s ≠ 0)
    (hloc0 : (∑ s ∈ range (t + 1), |Q₀ s - exactRootKernel S t s|) ≤ η₀)
    (hloc : ∀ S' s', count S' s' ≠ 0 →
      ∑ y ∈ range (s' + 1), |Q S' s' y - exactKernel S' s' y| ≤ η)
    (f : List Bool → ℚ) (hind : ∀ x, f x * f x = f x)
    (hf01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (N : ℕ) (hN : 0 < N) (a : ℚ) (ha : 0 < a) :
    (∑ v ∈ (vecs (maskFinset S.length) N).filter
        (fun v => a + (η₀ + η * internalNodes S) ≤
          |sumStat f v / N - expect1 (maskFinset S.length) (samplerMass S t) f|),
      prodMass (samplerMassK Q₀ Q S t) v) ≤
      1 / (4 * N * a ^ 2) := by
  set μ := samplerMass S t with hμ
  set μ' := samplerMassK Q₀ Q S t with hμ'
  set Δ := η₀ + η * (internalNodes S : ℚ) with hΔdef
  -- the approximate sampler is a genuine distribution
  have hμ'nn : ∀ m, 0 ≤ μ' m := by
    intro m
    rw [hμ']
    unfold samplerMassK
    apply Finset.sum_nonneg
    intro s _
    exact mul_nonneg (hQ₀nn s) (splitMassK_nonneg Q hQ.nonneg S s m)
  have hμ'tot : ∑ m ∈ maskFinset S.length, μ' m = 1 :=
    samplerMassK_total Q₀ Q hQ S t hQ₀tot hQ₀supp
  -- Stage B: per-sample L1 damage
  have hl1 : (∑ m ∈ maskFinset S.length, |μ' m - μ m|) ≤ Δ :=
    samplerMassK_l1 Q₀ Q hQ S t η₀ η hQ₀nn hQ₀supp hloc0 hloc
  -- expectations are close
  have hexp : |expect1 (maskFinset S.length) μ' f -
      expect1 (maskFinset S.length) μ f| ≤ Δ :=
    le_trans (expect1_l1 _ μ μ' f hf01) hl1
  -- event inclusion: far from the exact mean → far from the approximate mean
  have hsub : (vecs (maskFinset S.length) N).filter
      (fun v => a + Δ ≤ |sumStat f v / N - expect1 (maskFinset S.length) μ f|) ⊆
      (vecs (maskFinset S.length) N).filter
      (fun v => a ≤ |sumStat f v / N - expect1 (maskFinset S.length) μ' f|) := by
    intro v hv
    rw [Finset.mem_filter] at hv ⊢
    refine ⟨hv.1, ?_⟩
    have htri : |sumStat f v / N - expect1 (maskFinset S.length) μ f| ≤
        |sumStat f v / N - expect1 (maskFinset S.length) μ' f| +
          |expect1 (maskFinset S.length) μ' f -
            expect1 (maskFinset S.length) μ f| := abs_sub_le _ _ _
    have h2 := hv.2
    linarith [hexp]
  calc (∑ v ∈ (vecs (maskFinset S.length) N).filter
        (fun v => a + Δ ≤
          |sumStat f v / N - expect1 (maskFinset S.length) μ f|),
      prodMass μ' v)
      ≤ ∑ v ∈ (vecs (maskFinset S.length) N).filter
        (fun v => a ≤ |sumStat f v / N - expect1 (maskFinset S.length) μ' f|),
          prodMass μ' v :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun v _ _ => prodMass_nonneg μ' hμ'nn v)
    _ ≤ 1 / (4 * N * a ^ 2) :=
        estimator_chebyshev (maskFinset S.length) μ' hμ'nn hμ'tot
          f hind hf01 N hN a ha
