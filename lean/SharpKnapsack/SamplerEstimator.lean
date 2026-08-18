/-
# Stage C of the witness-sampler verification: the Monte Carlo estimator

The FPRAS estimates a probability `p` by drawing `N` independent samples
from the sampler's distribution `μ` and averaging an indicator. This file
formalizes that estimator over an arbitrary finite sample space, with no
measure theory: the space of `N`-vectors is a `Finset` of lists, the
product mass is a product of rationals, and expectation/variance are
finite sums. The deliverables:

* `prodMass_total` - the vectors carry total mass one;
* `sum_dev_zero` / `sum_sq_dev` - mean and variance of the empirical sum
  (independence enters through the product structure: the cross term
  vanishes);
* `estimator_chebyshev` - the Chebyshev tail bound
  `P(|p̂ - p| ≥ a) ≤ 1/(4·N·a²)` for indicator statistics, the exact
  sample-complexity engine of the algorithm's `ε⁻²` term.
-/
import SharpKnapsack.SamplerApprox

open Finset

variable {α : Type}

/-- Cons as an embedding, to build the vector space of samples. -/
def consEmb (α : Type) : α × List α ↪ List α :=
  ⟨fun p => p.1 :: p.2, by
    intro a b h
    simp only [List.cons.injEq] at h
    exact Prod.ext h.1 h.2⟩

/-- All `N`-vectors of samples from `Ω`. -/
def vecs (Ω : Finset α) : ℕ → Finset (List α)
  | 0 => {[]}
  | N + 1 => ((Ω ×ˢ vecs Ω N).map (consEmb α))

/-- Product mass of a vector of independent draws. -/
def prodMass (μ : α → ℚ) : List α → ℚ
  | [] => 1
  | x :: xs => μ x * prodMass μ xs

theorem sum_vecs_succ (Ω : Finset α) (N : ℕ) (F : List α → ℚ) :
    (∑ v ∈ vecs Ω (N + 1), F v) = ∑ x ∈ Ω, ∑ xs ∈ vecs Ω N, F (x :: xs) := by
  rw [vecs, Finset.sum_map, Finset.sum_product]
  rfl

/-- Nested sums of products factorize. -/
theorem sum_sum_factor (A : Finset α) (B : Finset (List α))
    (g : α → ℚ) (h : List α → ℚ) :
    (∑ x ∈ A, ∑ xs ∈ B, g x * h xs) = (∑ x ∈ A, g x) * ∑ xs ∈ B, h xs := by
  rw [Finset.sum_mul_sum]

theorem prodMass_total (Ω : Finset α) (μ : α → ℚ) (htot : ∑ x ∈ Ω, μ x = 1) :
    ∀ N, ∑ v ∈ vecs Ω N, prodMass μ v = 1 := by
  intro N
  induction N with
  | zero => simp [vecs, prodMass]
  | succ N ih =>
    rw [sum_vecs_succ]
    have h : ∀ x ∈ Ω, (∑ xs ∈ vecs Ω N, prodMass μ (x :: xs)) =
        ∑ xs ∈ vecs Ω N, μ x * prodMass μ xs :=
      fun x _ => Finset.sum_congr rfl fun xs _ => rfl
    rw [Finset.sum_congr rfl h, sum_sum_factor, htot, ih, one_mul]

theorem prodMass_nonneg (μ : α → ℚ) (hnn : ∀ x, 0 ≤ μ x) (v : List α) :
    0 ≤ prodMass μ v := by
  induction v with
  | nil => norm_num [prodMass]
  | cons x xs ih => exact mul_nonneg (hnn x) ih

/-- The empirical sum statistic. -/
def sumStat (f : α → ℚ) (v : List α) : ℚ := (v.map f).sum

/-- One-sample expectation. -/
def expect1 (Ω : Finset α) (μ : α → ℚ) (f : α → ℚ) : ℚ := ∑ x ∈ Ω, μ x * f x

/-- The first moment of the centered statistic vanishes. -/
theorem sum_dev_zero (Ω : Finset α) (μ : α → ℚ) (htot : ∑ x ∈ Ω, μ x = 1)
    (f : α → ℚ) :
    ∀ N, (∑ v ∈ vecs Ω N,
      prodMass μ v * (sumStat f v - N * expect1 Ω μ f)) = 0 := by
  intro N
  induction N with
  | zero => simp [vecs, prodMass, sumStat]
  | succ N ih =>
    rw [sum_vecs_succ]
    push_cast
    set e := expect1 Ω μ f with he
    have h : ∀ x ∈ Ω, (∑ xs ∈ vecs Ω N,
        prodMass μ (x :: xs) * (sumStat f (x :: xs) - ((N : ℚ) + 1) * e)) =
        (∑ xs ∈ vecs Ω N, (μ x * (f x - e)) * prodMass μ xs)
          + ∑ xs ∈ vecs Ω N, μ x * (prodMass μ xs * (sumStat f xs - N * e)) := by
      intro x _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro xs _
      show μ x * prodMass μ xs * (f x + sumStat f xs - ((N : ℚ) + 1) * e) = _
      ring
    rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, sum_sum_factor,
      sum_sum_factor, prodMass_total Ω μ htot N, mul_one]
    have hcast : (∑ xs ∈ vecs Ω N,
        prodMass μ xs * (sumStat f xs - (N : ℚ) * e)) = 0 := by
      exact_mod_cast ih
    rw [hcast, htot]
    have h3 : (∑ x ∈ Ω, μ x * (f x - e)) = 0 := by
      have h4 : ∀ x ∈ Ω, μ x * (f x - e) = μ x * f x - e * μ x :=
        fun x _ => by ring
      rw [Finset.sum_congr rfl h4, Finset.sum_sub_distrib, ← Finset.mul_sum,
        htot, mul_one, ← expect1, ← he]
      ring
    rw [h3]
    ring

/-- Variance additivity for independent draws: the second moment of the
centered sum is `N` times the one-sample variance. The cross term vanishes
by `sum_dev_zero` - this is where independence does its work. -/
theorem sum_sq_dev (Ω : Finset α) (μ : α → ℚ) (htot : ∑ x ∈ Ω, μ x = 1)
    (f : α → ℚ) :
    ∀ N, (∑ v ∈ vecs Ω N,
      prodMass μ v * (sumStat f v - N * expect1 Ω μ f) ^ 2) =
      N * expect1 Ω μ (fun x => (f x - expect1 Ω μ f) ^ 2) := by
  intro N
  induction N with
  | zero => simp [vecs, prodMass, sumStat]
  | succ N ih =>
    rw [sum_vecs_succ]
    push_cast
    set e := expect1 Ω μ f with he
    have h : ∀ x ∈ Ω, (∑ xs ∈ vecs Ω N,
        prodMass μ (x :: xs) * (sumStat f (x :: xs) - ((N : ℚ) + 1) * e) ^ 2) =
        (∑ xs ∈ vecs Ω N, (μ x * (f x - e) ^ 2) * prodMass μ xs)
          + (∑ xs ∈ vecs Ω N,
              (2 * (μ x * (f x - e))) * (prodMass μ xs * (sumStat f xs - N * e)))
          + ∑ xs ∈ vecs Ω N, μ x * (prodMass μ xs * (sumStat f xs - N * e) ^ 2) := by
      intro x _
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro xs _
      show μ x * prodMass μ xs * (f x + sumStat f xs - ((N : ℚ) + 1) * e) ^ 2 = _
      ring
    rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, Finset.sum_add_distrib,
      sum_sum_factor, sum_sum_factor, sum_sum_factor,
      prodMass_total Ω μ htot N, mul_one]
    have hdev : (∑ xs ∈ vecs Ω N,
        prodMass μ xs * (sumStat f xs - (N : ℚ) * e)) = 0 := by
      exact_mod_cast sum_dev_zero Ω μ htot f N
    have hIH : (∑ xs ∈ vecs Ω N,
        prodMass μ xs * (sumStat f xs - (N : ℚ) * e) ^ 2) =
        (N : ℚ) * expect1 Ω μ (fun x => (f x - e) ^ 2) := by
      exact_mod_cast ih
    rw [hdev, hIH, htot]
    have h6 : (∑ x ∈ Ω, μ x * (f x - e) ^ 2) =
        expect1 Ω μ (fun x => (f x - e) ^ 2) := rfl
    rw [h6]
    ring

/-- **Chebyshev tail bound for the Monte Carlo estimator.** For an
indicator statistic (`f² = f`, `0 ≤ f ≤ 1`), the probability that the
empirical mean deviates from `p = expect1 f` by at least `a` is at most
`1/(4·N·a²)`. -/
theorem estimator_chebyshev (Ω : Finset α) (μ : α → ℚ)
    (hnn : ∀ x, 0 ≤ μ x) (htot : ∑ x ∈ Ω, μ x = 1)
    (f : α → ℚ) (hind : ∀ x, f x * f x = f x) (hf01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (N : ℕ) (hN : 0 < N) (a : ℚ) (ha : 0 < a) :
    (∑ v ∈ (vecs Ω N).filter
        (fun v => a ≤ |sumStat f v / N - expect1 Ω μ f|), prodMass μ v) ≤
      1 / (4 * N * a ^ 2) := by
  set e := expect1 Ω μ f with he
  have hNQ : (0:ℚ) < (N : ℚ) := by exact_mod_cast hN
  have hmarkov : ∀ v ∈ (vecs Ω N).filter
      (fun v => a ≤ |sumStat f v / N - e|),
      prodMass μ v ≤ prodMass μ v * (sumStat f v - N * e) ^ 2 / (N * a) ^ 2 := by
    intro v hv
    rw [Finset.mem_filter] at hv
    have hdev : (N : ℚ) * a ≤ |sumStat f v - N * e| := by
      have h1 : sumStat f v / N - e = (sumStat f v - N * e) / N := by
        field_simp
      have h2 := hv.2
      rw [h1, abs_div, abs_of_pos hNQ, le_div_iff₀ hNQ] at h2
      linarith
    have hsq : ((N : ℚ) * a) ^ 2 ≤ (sumStat f v - N * e) ^ 2 := by
      have h2 : ((N : ℚ) * a) ^ 2 ≤ |sumStat f v - N * e| ^ 2 :=
        pow_le_pow_left₀ (by positivity) hdev 2
      rwa [sq_abs] at h2
    rw [le_div_iff₀ (by positivity)]
    exact mul_le_mul_of_nonneg_left hsq (prodMass_nonneg μ hnn v)
  refine le_trans (Finset.sum_le_sum hmarkov) ?_
  have hfull : (∑ v ∈ (vecs Ω N).filter
      (fun v => a ≤ |sumStat f v / N - e|),
        prodMass μ v * (sumStat f v - N * e) ^ 2 / (N * a) ^ 2) ≤
      ∑ v ∈ vecs Ω N, prodMass μ v * (sumStat f v - N * e) ^ 2 / (N * a) ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro v _ _
    have h := prodMass_nonneg μ hnn v
    positivity
  refine le_trans hfull ?_
  rw [← Finset.sum_div, sum_sq_dev Ω μ htot f N]
  have hvar : expect1 Ω μ (fun x => (f x - e) ^ 2) ≤ 1 / 4 := by
    have hpe : 0 ≤ e := by
      rw [he, expect1]
      exact Finset.sum_nonneg fun x _ => mul_nonneg (hnn x) (hf01 x).1
    have hpe1 : e ≤ 1 := by
      rw [he, expect1]
      calc (∑ x ∈ Ω, μ x * f x) ≤ ∑ x ∈ Ω, μ x := by
            apply Finset.sum_le_sum
            intro x _
            calc μ x * f x ≤ μ x * 1 :=
                  mul_le_mul_of_nonneg_left (hf01 x).2 (hnn x)
              _ = μ x := mul_one _
        _ = 1 := htot
    have hexp : expect1 Ω μ (fun x => (f x - e) ^ 2) = e - e ^ 2 := by
      have h5 : ∀ x ∈ Ω, μ x * (f x - e) ^ 2 =
          μ x * f x * f x - 2 * e * (μ x * f x) + e ^ 2 * μ x := fun x _ => by ring
      show (∑ x ∈ Ω, μ x * (f x - e) ^ 2) = e - e ^ 2
      rw [Finset.sum_congr rfl h5, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      have h6 : (∑ x ∈ Ω, μ x * f x * f x) = e := by
        rw [he, expect1]
        apply Finset.sum_congr rfl
        intro x _
        rw [mul_assoc, hind x]
      have h7 : (∑ x ∈ Ω, 2 * e * (μ x * f x)) = 2 * e * e := by
        rw [← Finset.mul_sum, ← expect1, ← he]
      have h8 : (∑ x ∈ Ω, e ^ 2 * μ x) = e ^ 2 := by
        rw [← Finset.mul_sum, htot, mul_one]
      rw [h6, h7, h8]
      ring
    rw [hexp]
    nlinarith [sq_nonneg (2 * e - 1)]
  calc (N : ℚ) * expect1 Ω μ (fun x => (f x - e) ^ 2) / (N * a) ^ 2
      ≤ (N : ℚ) * (1 / 4) / (N * a) ^ 2 := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hvar (le_of_lt hNQ))
          (by positivity)
    _ = 1 / (4 * N * a ^ 2) := by
        field_simp

/-! ### C.2: robustness - the estimator tolerates an approximate sampler

The samples actually come from the Stage-B kernel sampler, not the exact
uniform. Product-measure L1 subadditivity converts the per-sample L1 bound
into a bound on any event probability over the whole run: TV damage grows
only linearly in `N`. -/
theorem prodMass_l1 (Ω : Finset α) (μ μ' : α → ℚ)
    (hnn : ∀ x, 0 ≤ μ x) (hnn' : ∀ x, 0 ≤ μ' x)
    (htot : ∑ x ∈ Ω, μ x = 1) (htot' : ∑ x ∈ Ω, μ' x = 1) :
    ∀ N, (∑ v ∈ vecs Ω N, |prodMass μ' v - prodMass μ v|) ≤
      N * ∑ x ∈ Ω, |μ' x - μ x| := by
  intro N
  induction N with
  | zero => simp [vecs, prodMass]
  | succ N ih =>
    rw [sum_vecs_succ]
    push_cast
    have h : ∀ x ∈ Ω, (∑ xs ∈ vecs Ω N,
        |prodMass μ' (x :: xs) - prodMass μ (x :: xs)|) ≤
        (∑ xs ∈ vecs Ω N, |μ' x - μ x| * prodMass μ' xs)
          + ∑ xs ∈ vecs Ω N, μ x * |prodMass μ' xs - prodMass μ xs| := by
      intro x _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro xs _
      show |μ' x * prodMass μ' xs - μ x * prodMass μ xs| ≤ _
      exact hybrid_abs2 (μ' x) (μ x) (prodMass μ' xs) (prodMass μ xs)
        (prodMass_nonneg μ' hnn' xs) (hnn x)
    refine le_trans (Finset.sum_le_sum h) ?_
    rw [Finset.sum_add_distrib, sum_sum_factor, sum_sum_factor,
      prodMass_total Ω μ' htot' N, mul_one, htot, one_mul]
    have hd : 0 ≤ ∑ x ∈ Ω, |μ' x - μ x| :=
      Finset.sum_nonneg fun x _ => abs_nonneg _
    have hihq : (∑ xs ∈ vecs Ω N, |prodMass μ' xs - prodMass μ xs|) ≤
        (N : ℚ) * ∑ x ∈ Ω, |μ' x - μ x| := by exact_mod_cast ih
    linarith

/-- Any event's probability moves by at most the full-run L1 distance. -/
theorem event_prob_diff (Ω : Finset α) (μ μ' : α → ℚ) (N : ℕ)
    (E : Finset (List α)) (hE : E ⊆ vecs Ω N) :
    |(∑ v ∈ E, prodMass μ' v) - ∑ v ∈ E, prodMass μ v| ≤
      ∑ v ∈ vecs Ω N, |prodMass μ' v - prodMass μ v| := by
  rw [← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  exact Finset.sum_le_sum_of_subset_of_nonneg hE (fun v _ _ => abs_nonneg _)
