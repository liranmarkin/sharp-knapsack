/-
# Stage E.2 of the witness-sampler verification: the ledger sums

The per-sample cost of the witness sampler is
`Σ_h min(2^h, k) · (per-node work at depth h)`, with per-node work
`min(items/2^h, L/2^(h/2))`-shaped. This file machine-checks the two
bounding modes used in the cost ledger of `docs/witness-sampler.md`:

* `ledger_flat` - the `items/2^h` mode telescopes to `D·A` (absorbed in Õ);
* `ledger_sqrt` - the `L/2^(h/2)` mode sums to `O(L·√k)` - the source of
  the `n√ℓ` term, and with Stage 0's `ledger_collapse`, of `n^{4/3}`.

Everything is ℕ-arithmetic; the geometric tools are proven from scratch.
-/
import SharpKnapsack.SamplerExact

open Finset

/-- Halving geometric sums of ℕ-divisions are bounded by `2Y`. -/
theorem geom_sum_le (K : ℕ) : ∀ Y : ℕ, (∑ i ∈ range K, Y / 2 ^ i) ≤ 2 * Y := by
  induction K with
  | zero => intro Y; simp
  | succ K ih =>
    intro Y
    rw [Finset.sum_range_succ']
    have h : ∀ i, Y / 2 ^ (i + 1) = (Y / 2) / 2 ^ i := by
      intro i
      rw [pow_succ']
      rw [Nat.div_div_eq_div_mul]
    simp only [h, pow_zero, Nat.div_one]
    have := ih (Y / 2)
    omega

/-- The half-index geometric sum: `Σ_j Y/2^(j/2) ≤ 4Y`. -/
theorem geom_half_root (M Y : ℕ) : (∑ j ∈ range M, Y / 2 ^ (j / 2)) ≤ 4 * Y := by
  -- pair up the indices: j = 2i and j = 2i+1 both contribute Y/2^i
  have hpair : ∀ K, (∑ j ∈ range (2 * K), Y / 2 ^ (j / 2)) =
      2 * ∑ i ∈ range K, Y / 2 ^ i := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      have h2 : 2 * (K + 1) = (2 * K + 1) + 1 := by omega
      rw [h2, Finset.sum_range_succ, Finset.sum_range_succ, ih,
        Finset.sum_range_succ]
      have e1 : (2 * K) / 2 = K := by omega
      have e2 : (2 * K + 1) / 2 = K := by omega
      rw [e1, e2]
      ring
  calc (∑ j ∈ range M, Y / 2 ^ (j / 2))
      ≤ ∑ j ∈ range (2 * ((M + 1) / 2)), Y / 2 ^ (j / 2) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro j hj
          rw [Finset.mem_range] at hj ⊢
          omega
        · intro j _ _
          exact Nat.zero_le _
    _ = 2 * ∑ i ∈ range ((M + 1) / 2), Y / 2 ^ i := hpair _
    _ ≤ 2 * (2 * Y) := by
        have := geom_sum_le ((M + 1) / 2) Y
        omega
    _ = 4 * Y := by ring

/-- The staircase sum: `Σ_h 2^((h+1)/2) ≤ 2^(M/2 + 2)`. -/
theorem staircase_le : ∀ M : ℕ, (∑ h ∈ range M, 2 ^ ((h + 1) / 2)) ≤ 2 ^ (M / 2 + 2) := by
  intro M
  induction M using Nat.strong_induction_on with
  | _ M IH =>
  rcases M with _ | _ | M
  · simp
  · simp
  · have hIH := IH M (by omega)
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have e1 : (M + 1 + 1) / 2 = M / 2 + 1 := by omega
    rw [e1, show M / 2 + 1 + 2 = M / 2 + 3 from by omega]
    have h1 : 2 ^ ((M + 1) / 2) ≤ 2 * 2 ^ (M / 2) := by
      calc 2 ^ ((M + 1) / 2)
          ≤ 2 ^ (M / 2 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 2 * 2 ^ (M / 2) := by rw [pow_succ]; ring
    have h4 : (2:ℕ) ^ (M / 2 + 1) = 2 * 2 ^ (M / 2) := by rw [pow_succ]; ring
    have h5 : (2:ℕ) ^ (M / 2 + 2) = 4 * 2 ^ (M / 2) := by rw [pow_add]; norm_num; ring
    have h6 : (2:ℕ) ^ (M / 2 + 3) = 8 * 2 ^ (M / 2) := by rw [pow_add]; norm_num; ring
    rw [h5] at hIH
    omega

/-- Ledger mode (i): the `items/2^h` work telescopes to `D · A` -
absorbed by the polylog in the Õ. -/
theorem ledger_flat (A k D : ℕ) :
    (∑ h ∈ range D, min (2 ^ h) k * (A / 2 ^ h)) ≤ D * A := by
  calc (∑ h ∈ range D, min (2 ^ h) k * (A / 2 ^ h))
      ≤ ∑ _h ∈ range D, A := by
        apply Finset.sum_le_sum
        intro h _
        calc min (2 ^ h) k * (A / 2 ^ h) ≤ 2 ^ h * (A / 2 ^ h) :=
              Nat.mul_le_mul_right _ (min_le_left _ _)
          _ ≤ A := by
              rw [mul_comm]
              exact Nat.div_mul_le_self A (2 ^ h)
    _ = D * A := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- **Ledger mode (ii)**: the `L/2^(h/2)` work sums to `O(L·√k)` over a
pruned descent with `k` items - the machine-checked source of the `n√ℓ`
term in the running-time bound. -/
theorem ledger_sqrt (B k D : ℕ) :
    (∑ h ∈ range D, min (2 ^ h) k * (B / 2 ^ (h / 2))) ≤
      32 * B * (Nat.sqrt k + 1) := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · subst hk0
    simp
  set H := Nat.log 2 k with hH
  have h2H : 2 ^ H ≤ k := Nat.pow_log_le_self 2 (by omega)
  have hk2 : k < 2 ^ (H + 1) := Nat.lt_pow_succ_log_self (by norm_num) k
  have hsqrt : 2 ^ (H / 2) ≤ Nat.sqrt k := by
    apply Nat.le_sqrt.mpr
    calc 2 ^ (H / 2) * 2 ^ (H / 2) = 2 ^ (H / 2 + H / 2) := by rw [pow_add]
      _ ≤ 2 ^ H := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ k := h2H
  -- per-term bound
  have hterm : ∀ h ∈ range D, min (2 ^ h) k * (B / 2 ^ (h / 2)) ≤
      (if h < H + 2 then B * 2 ^ ((h + 1) / 2) else (k * B) / 2 ^ (h / 2)) := by
    intro h _
    by_cases hh : h < H + 2
    · rw [if_pos hh]
      have hsplitexp : (2:ℕ) ^ h = 2 ^ ((h + 1) / 2) * 2 ^ (h / 2) := by
        rw [← pow_add]
        congr 1
        omega
      calc min (2 ^ h) k * (B / 2 ^ (h / 2))
          ≤ 2 ^ h * (B / 2 ^ (h / 2)) :=
            Nat.mul_le_mul_right _ (min_le_left _ _)
        _ = 2 ^ ((h + 1) / 2) * (2 ^ (h / 2) * (B / 2 ^ (h / 2))) := by
            rw [hsplitexp]
            ring
        _ ≤ 2 ^ ((h + 1) / 2) * B := by
            apply Nat.mul_le_mul_left
            rw [mul_comm]
            exact Nat.div_mul_le_self B (2 ^ (h / 2))
        _ = B * 2 ^ ((h + 1) / 2) := Nat.mul_comm _ _
    · rw [if_neg hh]
      calc min (2 ^ h) k * (B / 2 ^ (h / 2))
          ≤ k * (B / 2 ^ (h / 2)) :=
            Nat.mul_le_mul_right _ (min_le_right _ _)
        _ ≤ (k * B) / 2 ^ (h / 2) := by
            rw [Nat.le_div_iff_mul_le (by positivity)]
            calc k * (B / 2 ^ (h / 2)) * 2 ^ (h / 2)
                = k * (B / 2 ^ (h / 2) * 2 ^ (h / 2)) := by ring
              _ ≤ k * B :=
                  Nat.mul_le_mul_left _ (Nat.div_mul_le_self B (2 ^ (h / 2)))
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_ite]
  -- part 1: the staircase below the crossover
  have hpart1 : (∑ h ∈ (range D).filter (fun h => h < H + 2), B * 2 ^ ((h + 1) / 2)) ≤
      8 * B * Nat.sqrt k := by
    calc (∑ h ∈ (range D).filter (fun h => h < H + 2), B * 2 ^ ((h + 1) / 2))
        ≤ ∑ h ∈ range (H + 2), B * 2 ^ ((h + 1) / 2) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro h hh
            rw [Finset.mem_filter, Finset.mem_range] at hh
            rw [Finset.mem_range]
            exact hh.2
          · intro h _ _
            exact Nat.zero_le _
      _ = B * ∑ h ∈ range (H + 2), 2 ^ ((h + 1) / 2) := by rw [Finset.mul_sum]
      _ ≤ B * 2 ^ ((H + 2) / 2 + 2) :=
          Nat.mul_le_mul_left _ (staircase_le (H + 2))
      _ = B * (8 * 2 ^ (H / 2)) := by
          congr 1
          rw [show (H + 2) / 2 + 2 = H / 2 + 3 from by omega, pow_add]
          ring
      _ ≤ B * (8 * Nat.sqrt k) := by
          apply Nat.mul_le_mul_left
          exact Nat.mul_le_mul_left _ hsqrt
      _ = 8 * B * Nat.sqrt k := by ring
  -- part 2: the geometric tail above the crossover
  have hpart2 : (∑ h ∈ (range D).filter (fun h => ¬ h < H + 2),
      (k * B) / 2 ^ (h / 2)) ≤ 8 * B * Nat.sqrt k := by
    have hIco : (range D).filter (fun h => ¬ h < H + 2) = Finset.Ico (H + 2) D := by
      ext h
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      omega
    rw [hIco, Finset.sum_Ico_eq_sum_range]
    set Y := (k * B) / 2 ^ ((H + 2) / 2) with hY
    have hterm2 : ∀ j ∈ range (D - (H + 2)),
        (k * B) / 2 ^ ((H + 2 + j) / 2) ≤ Y / 2 ^ (j / 2) := by
      intro j _
      have hexp : (H + 2) / 2 + j / 2 ≤ (H + 2 + j) / 2 := by omega
      have hle : (2:ℕ) ^ ((H + 2) / 2) * 2 ^ (j / 2) ≤ 2 ^ ((H + 2 + j) / 2) := by
        rw [← pow_add]
        exact Nat.pow_le_pow_right (by norm_num) hexp
      calc (k * B) / 2 ^ ((H + 2 + j) / 2)
          ≤ (k * B) / (2 ^ ((H + 2) / 2) * 2 ^ (j / 2)) :=
            Nat.div_le_div_left hle (by positivity)
        _ = Y / 2 ^ (j / 2) := by
            rw [hY, Nat.div_div_eq_div_mul]
    calc (∑ j ∈ range (D - (H + 2)), (k * B) / 2 ^ ((H + 2 + j) / 2))
        ≤ ∑ j ∈ range (D - (H + 2)), Y / 2 ^ (j / 2) :=
          Finset.sum_le_sum hterm2
      _ ≤ 4 * Y := geom_half_root _ Y
      _ ≤ 8 * B * Nat.sqrt k := by
          have hYle : Y ≤ 2 * B * Nat.sqrt k := by
            have h1 : Y ≤ (2 ^ (H + 1) * B) / 2 ^ ((H + 2) / 2) := by
              rw [hY]
              exact Nat.div_le_div_right (Nat.mul_le_mul_right _ (le_of_lt hk2))
            have h2 : (2:ℕ) ^ (H + 1) * B / 2 ^ ((H + 2) / 2) =
                2 ^ (H + 1 - (H + 2) / 2) * B := by
              have hsplit : (2:ℕ) ^ (H + 1) = 2 ^ ((H + 2) / 2) * 2 ^ (H + 1 - (H + 2) / 2) := by
                rw [← pow_add]
                congr 1
                omega
              rw [hsplit, mul_assoc]
              exact Nat.mul_div_cancel_left _ (by positivity)
            have h3 : (2:ℕ) ^ (H + 1 - (H + 2) / 2) ≤ 2 * 2 ^ (H / 2) := by
              calc (2:ℕ) ^ (H + 1 - (H + 2) / 2) ≤ 2 ^ (H / 2 + 1) :=
                    Nat.pow_le_pow_right (by norm_num) (by omega)
                _ = 2 * 2 ^ (H / 2) := by rw [pow_succ]; ring
            calc Y ≤ 2 ^ (H + 1 - (H + 2) / 2) * B := h2 ▸ h1
              _ ≤ (2 * 2 ^ (H / 2)) * B := Nat.mul_le_mul_right _ h3
              _ ≤ (2 * Nat.sqrt k) * B := by
                  apply Nat.mul_le_mul_right
                  exact Nat.mul_le_mul_left _ hsqrt
              _ = 2 * B * Nat.sqrt k := by ring
          have h8 : 8 * B * Nat.sqrt k = 4 * (2 * B * Nat.sqrt k) := by ring
          omega
  calc (∑ h ∈ (range D).filter (fun h => h < H + 2), B * 2 ^ ((h + 1) / 2)) +
        ∑ h ∈ (range D).filter (fun h => ¬ h < H + 2), (k * B) / 2 ^ (h / 2)
      ≤ 8 * B * Nat.sqrt k + 8 * B * Nat.sqrt k := add_le_add hpart1 hpart2
    _ ≤ 32 * B * (Nat.sqrt k + 1) := by nlinarith [Nat.zero_le (B * Nat.sqrt k)]
