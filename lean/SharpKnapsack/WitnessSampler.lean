/-
The load-bearing new lemmas of the witness sampler
(`docs/research/2026-08-18-witness-sampler-proof.md`), machine-checked.

1. `witness_product_identity` - Lemma 1's algebraic core: on a witness pair
   the residual product times the level scale reconstructs the true product
   exactly. This is what makes the sampler factorize the stored arrays with
   zero TV cost at every split.
2. `diagonal_witness_domination` - Lemma 2: with 3-separated levels the
   non-attaining diagonal mass is at most a δ-fraction of the attaining mass.
3. `lazy_amortization` - Lemma 3's counting bound for the lazily built
   dyadic-pair correlations.
4. `ledger_collapse` - the final ledger arithmetic
   min(n·√ℓ, n²/ℓ)³ ≤ n⁴, i.e. the sampling term is at most n^{4/3}.
-/
import Mathlib

namespace SharpKnapsack

/-! ### Lemma 1: exact witness decomposition -/

/-- On a witness pair (levels `a + b = C`), the product of residuals
`f/D^a` and `g/D^b` scaled back by `D^C` is exactly `f·g`. -/
theorem witness_product_identity (D f g : ℚ) (a b C : ℤ) (hD : D ≠ 0)
    (hab : a + b = C) :
    f / D ^ a * (g / D ^ b) * D ^ C = f * g := by
  subst hab
  rw [zpow_add₀ hD, div_mul_div_comm]
  rw [div_mul_eq_mul_div, mul_div_assoc]
  rw [div_self (by exact mul_ne_zero (zpow_ne_zero a hD) (zpow_ne_zero b hD))]
  ring

/-! ### Lemma 2: diagonal domination -/

/-- Diagonal pairs at fine position `s` are indexed by `x ∈ P ⊆ range (s+1)`
(the support), with mass `w x`, level sum `lv x`, and the level sandwich
`D ^ lv x ≤ w x < D ^ (lv x + 2)` (product of two one-sided sandwiches).
`C` is the maximal level sum, attained somewhere; level sums are 3-separated
below `C`. Then the non-attaining mass is at most `δ` times the attaining
mass, provided `(s+1 : ℚ) ≤ δ·D`. -/
theorem diagonal_witness_domination
    (s : ℕ) (P : Finset ℕ) (hP : P ⊆ Finset.range (s + 1))
    (w : ℕ → ℚ) (lv : ℕ → ℤ) (D δ : ℚ) (C : ℤ)
    (hD : 1 < D) (hδ : 0 < δ)
    (hlo : ∀ x ∈ P, D ^ lv x ≤ w x)
    (hhi : ∀ x ∈ P, w x < D ^ (lv x + 2))
    (hsep : ∀ x ∈ P, lv x = C ∨ lv x + 3 ≤ C)
    (hatt : ∃ x₀ ∈ P, lv x₀ = C)
    (hs : (s + 1 : ℚ) ≤ δ * D) :
    ∑ x ∈ P with lv x ≠ C, w x ≤ δ * ∑ x ∈ P with lv x = C, w x := by
  have hD0 : (0 : ℚ) < D := lt_trans one_pos hD
  have hterm : ∀ x ∈ P, lv x ≠ C → w x ≤ D ^ (C - 1) := by
    intro x hx hne
    rcases hsep x hx with h | h
    · exact absurd h hne
    · refine le_trans (le_of_lt (hhi x hx)) ?_
      apply zpow_le_zpow_right₀ (le_of_lt hD)
      omega
  have hcard : ((P.filter (fun x => lv x ≠ C)).card : ℚ) ≤ (s + 1 : ℚ) := by
    have h1 : (P.filter (fun x => lv x ≠ C)).card ≤ (Finset.range (s + 1)).card :=
      Finset.card_le_card (le_trans (Finset.filter_subset _ _) hP)
    rw [Finset.card_range] at h1
    exact_mod_cast h1
  have hsum : ∑ x ∈ P with lv x ≠ C, w x ≤ (s + 1 : ℚ) * D ^ (C - 1) := by
    calc ∑ x ∈ P with lv x ≠ C, w x
        ≤ ∑ _x ∈ P.filter (fun x => lv x ≠ C), D ^ (C - 1) := by
          apply Finset.sum_le_sum
          intro x hx
          rw [Finset.mem_filter] at hx
          exact hterm x hx.1 hx.2
      _ = ((P.filter (fun x => lv x ≠ C)).card : ℚ) * D ^ (C - 1) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (s + 1 : ℚ) * D ^ (C - 1) := by
          apply mul_le_mul_of_nonneg_right hcard
          positivity
  obtain ⟨x₀, hx₀, hlv₀⟩ := hatt
  have hattsum : D ^ C ≤ ∑ x ∈ P with lv x = C, w x := by
    have hx₀' : x₀ ∈ P.filter (fun x => lv x = C) := by
      rw [Finset.mem_filter]; exact ⟨hx₀, hlv₀⟩
    calc D ^ C = D ^ lv x₀ := by rw [hlv₀]
      _ ≤ w x₀ := hlo x₀ hx₀
      _ ≤ ∑ x ∈ P with lv x = C, w x := by
          refine Finset.single_le_sum (fun x hx => ?_) hx₀'
          rw [Finset.mem_filter] at hx
          exact le_trans (by positivity : (0:ℚ) ≤ D ^ lv x) (hlo x hx.1)
  calc ∑ x ∈ P with lv x ≠ C, w x
      ≤ (s + 1 : ℚ) * D ^ (C - 1) := hsum
    _ ≤ δ * D * D ^ (C - 1) := by
        apply mul_le_mul_of_nonneg_right hs
        positivity
    _ = δ * D ^ C := by
        have h := zpow_add₀ (ne_of_gt hD0) (1 : ℤ) (C - 1)
        simp only [zpow_one] at h
        have hDC : D ^ C = D * D ^ (C - 1) := by
          rw [← h]
          congr 1
          ring
        rw [hDC]
        ring
    _ ≤ δ * ∑ x ∈ P with lv x = C, w x :=
        mul_le_mul_of_nonneg_left hattsum (le_of_lt hδ)

/-! ### Lemma 3: lazy amortization -/

/-- Per dyadic level `k`, the lazily built pair-correlations cost at most
`min(N·2^k, L²/2^k)`, and this is at most `(√N + 1)·L` by AM-GM. -/
theorem min_dyadic_le (N L c : ℕ) :
    min (N * c) (L ^ 2 / c) ≤ (Nat.sqrt N + 1) * L := by
  set x := min (N * c) (L ^ 2 / c) with hx
  have hsq : x * x ≤ N * L ^ 2 := by
    have h1 : x * x ≤ (N * c) * (L ^ 2 / c) :=
      Nat.mul_le_mul (min_le_left _ _) (min_le_right _ _)
    have h2 : (N * c) * (L ^ 2 / c) ≤ N * L ^ 2 := by
      rw [mul_assoc]
      have hc : c * (L ^ 2 / c) ≤ L ^ 2 := by
        rw [mul_comm]
        exact Nat.div_mul_le_self _ _
      exact Nat.mul_le_mul_left _ hc
    exact le_trans h1 h2
  have h4 : x ≤ Nat.sqrt (N * L ^ 2) := Nat.le_sqrt.mpr hsq
  have h5 : Nat.sqrt (N * L ^ 2) ≤ (Nat.sqrt N + 1) * L := by
    have hbig : N * L ^ 2 ≤ ((Nat.sqrt N + 1) * L) * ((Nat.sqrt N + 1) * L) := by
      have hN : N ≤ (Nat.sqrt N + 1) * (Nat.sqrt N + 1) := by
        have h := Nat.lt_succ_sqrt N
        simp only [Nat.succ_eq_add_one] at h
        exact le_of_lt h
      calc N * L ^ 2 ≤ ((Nat.sqrt N + 1) * (Nat.sqrt N + 1)) * L ^ 2 := by
            exact Nat.mul_le_mul_right _ hN
        _ = ((Nat.sqrt N + 1) * L) * ((Nat.sqrt N + 1) * L) := by ring
    calc Nat.sqrt (N * L ^ 2)
        ≤ Nat.sqrt (((Nat.sqrt N + 1) * L) * ((Nat.sqrt N + 1) * L)) :=
          Nat.sqrt_le_sqrt hbig
      _ = (Nat.sqrt N + 1) * L := Nat.sqrt_eq _
  exact le_trans h4 h5

/-- Total lazy-correlation build cost over `K+1` dyadic levels:
`Σ_k min(N·2^k, L²/2^k) ≤ (K+1)·(√N + 1)·L`. -/
theorem lazy_amortization (N L K : ℕ) :
    ∑ k ∈ Finset.range (K + 1), min (N * 2 ^ k) (L ^ 2 / 2 ^ k) ≤
      (K + 1) * ((Nat.sqrt N + 1) * L) := by
  calc ∑ k ∈ Finset.range (K + 1), min (N * 2 ^ k) (L ^ 2 / 2 ^ k)
      ≤ ∑ _k ∈ Finset.range (K + 1), (Nat.sqrt N + 1) * L :=
        Finset.sum_le_sum (fun k _ => min_dyadic_le N L (2 ^ k))
    _ = (K + 1) * ((Nat.sqrt N + 1) * L) := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

/-! ### The ledger collapse -/

/-- `min(n·√ℓ, n²/ℓ)³ ≤ n⁴`: the sampling term of the witness sampler is
at most `n^{4/3}` for every value of the popular-class parameter `ℓ`,
with the maximum at `ℓ = n^{2/3}`. -/
theorem ledger_collapse (n ℓ : ℕ) :
    (min (n * Nat.sqrt ℓ) (n ^ 2 / ℓ)) ^ 3 ≤ n ^ 4 := by
  set m := min (n * Nat.sqrt ℓ) (n ^ 2 / ℓ) with hm
  have h1 : m ≤ n * Nat.sqrt ℓ := min_le_left _ _
  have h2 : m ≤ n ^ 2 / ℓ := min_le_right _ _
  have key : m ^ 3 ≤ (n * Nat.sqrt ℓ) ^ 2 * (n ^ 2 / ℓ) := by
    calc m ^ 3 = m ^ 2 * m := by ring
      _ ≤ (n * Nat.sqrt ℓ) ^ 2 * (n ^ 2 / ℓ) :=
          Nat.mul_le_mul (Nat.pow_le_pow_left h1 2) h2
  have hsq : Nat.sqrt ℓ ^ 2 ≤ ℓ := Nat.sqrt_le' ℓ
  calc m ^ 3 ≤ (n * Nat.sqrt ℓ) ^ 2 * (n ^ 2 / ℓ) := key
    _ = n ^ 2 * Nat.sqrt ℓ ^ 2 * (n ^ 2 / ℓ) := by ring
    _ ≤ n ^ 2 * ℓ * (n ^ 2 / ℓ) := by
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hsq)
    _ = n ^ 2 * (ℓ * (n ^ 2 / ℓ)) := by ring
    _ ≤ n ^ 2 * n ^ 2 := by
        refine Nat.mul_le_mul_left _ ?_
        rw [mul_comm]
        exact Nat.div_mul_le_self _ _
    _ = n ^ 4 := by ring

end SharpKnapsack
