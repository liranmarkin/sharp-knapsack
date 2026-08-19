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
import SharpKnapsack.New.SamplerExact

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

/-! ### The construction ledger: the `n^{1.5}` accounting

Per tree level `h`: `2^h` nodes, arrays of length `L/2^(h/2)`, oracle cost
`length · √(value-range)` with range `M/2^h`. The balanced schedule makes
every level cost `O(L·√M)`; over `D+1` levels the total is
`O(D·L·√M)` - the machine-checked shape of the `Õ(n^{1.5})` construction
bound, with the oracle's own cost as the unit. -/

/-- `√(M/2^h)` is within one of `√M / 2^(h/2)`. -/
theorem sqrt_div_pow_le (M h : ℕ) :
    Nat.sqrt (M / 2 ^ h) ≤ Nat.sqrt M / 2 ^ (h / 2) + 1 := by
  set x := Nat.sqrt (M / 2 ^ h) with hx
  rcases Nat.eq_zero_or_pos x with h0 | hpos
  · rw [h0]
    exact Nat.zero_le _
  · have hxsq : x * x ≤ M / 2 ^ h := by
      have h := Nat.sqrt_le' (M / 2 ^ h)
      rw [pow_two] at h
      exact h
    have h1 : (x - 1) * 2 ^ (h / 2) ≤ Nat.sqrt M := by
      apply Nat.le_sqrt.mpr
      have e1 : (x - 1) * 2 ^ (h / 2) * ((x - 1) * 2 ^ (h / 2)) =
          ((x - 1) * (x - 1)) * (2 ^ (h / 2) * 2 ^ (h / 2)) := by ring
      rw [e1]
      have h2 : (x - 1) * (x - 1) ≤ x * x :=
        Nat.mul_le_mul (by omega) (by omega)
      have h3 : (2:ℕ) ^ (h / 2) * 2 ^ (h / 2) ≤ 2 ^ h := by
        rw [← pow_add]
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      calc ((x - 1) * (x - 1)) * (2 ^ (h / 2) * 2 ^ (h / 2))
          ≤ (M / 2 ^ h) * 2 ^ h := by
            apply Nat.mul_le_mul (le_trans h2 hxsq) h3
        _ ≤ M := by
            rw [mul_comm]
            exact Nat.mul_div_le M (2 ^ h)
    have h4 : x - 1 ≤ Nat.sqrt M / 2 ^ (h / 2) := by
      rw [Nat.le_div_iff_mul_le (by positivity)]
      exact h1
    omega

/-- **The construction ledger**: total oracle cost over the tree is
`O(D·L·(√M + 1))` - the `Õ(n^{1.5})` shape with the per-node oracle cost
`length·(√range + 1)` as the unit. -/
theorem construction_ledger (L M D : ℕ) (hD : 2 ^ D ≤ 2 * M) :
    (∑ h ∈ range (D + 1),
      (2 ^ h * (L / 2 ^ (h / 2))) * (Nat.sqrt (M / 2 ^ h) + 1)) ≤
      (2 * (D + 1) + 64) * (L * (Nat.sqrt M + 1)) := by
  have hterm : ∀ h ∈ range (D + 1),
      (2 ^ h * (L / 2 ^ (h / 2))) * (Nat.sqrt (M / 2 ^ h) + 1) ≤
        2 * (L * (Nat.sqrt M + 1)) + 2 * (L * 2 ^ ((h + 1) / 2)) := by
    intro h _
    have hlen : 2 ^ h * (L / 2 ^ (h / 2)) ≤ L * 2 ^ ((h + 1) / 2) := by
      have hsplitexp : (2:ℕ) ^ h = 2 ^ ((h + 1) / 2) * 2 ^ (h / 2) := by
        rw [← pow_add]
        congr 1
        omega
      calc 2 ^ h * (L / 2 ^ (h / 2))
          = 2 ^ ((h + 1) / 2) * (2 ^ (h / 2) * (L / 2 ^ (h / 2))) := by
            rw [hsplitexp]
            ring
        _ ≤ 2 ^ ((h + 1) / 2) * L := by
            apply Nat.mul_le_mul_left
            rw [mul_comm]
            exact Nat.div_mul_le_self L (2 ^ (h / 2))
        _ = L * 2 ^ ((h + 1) / 2) := Nat.mul_comm _ _
    have hsqrt := sqrt_div_pow_le M h
    -- split √M/2^(h/2) into the balanced part and the +2 slop
    have hbal : 2 ^ ((h + 1) / 2) * (Nat.sqrt M / 2 ^ (h / 2)) ≤
        2 * Nat.sqrt M := by
      have h5 : (2:ℕ) ^ ((h + 1) / 2) ≤ 2 * 2 ^ (h / 2) := by
        calc (2:ℕ) ^ ((h + 1) / 2) ≤ 2 ^ (h / 2 + 1) :=
              Nat.pow_le_pow_right (by norm_num) (by omega)
          _ = 2 * 2 ^ (h / 2) := by rw [pow_succ]; ring
      calc 2 ^ ((h + 1) / 2) * (Nat.sqrt M / 2 ^ (h / 2))
          ≤ (2 * 2 ^ (h / 2)) * (Nat.sqrt M / 2 ^ (h / 2)) :=
            Nat.mul_le_mul_right _ h5
        _ = 2 * (2 ^ (h / 2) * (Nat.sqrt M / 2 ^ (h / 2))) := by ring
        _ ≤ 2 * Nat.sqrt M := by
            apply Nat.mul_le_mul_left
            rw [mul_comm]
            exact Nat.div_mul_le_self _ _
    calc (2 ^ h * (L / 2 ^ (h / 2))) * (Nat.sqrt (M / 2 ^ h) + 1)
        ≤ (L * 2 ^ ((h + 1) / 2)) * (Nat.sqrt M / 2 ^ (h / 2) + 2) := by
          apply Nat.mul_le_mul hlen
          omega
      _ = L * (2 ^ ((h + 1) / 2) * (Nat.sqrt M / 2 ^ (h / 2))) +
          2 * (L * 2 ^ ((h + 1) / 2)) := by ring
      _ ≤ L * (2 * Nat.sqrt M) + 2 * (L * 2 ^ ((h + 1) / 2)) := by
          apply Nat.add_le_add_right
          exact Nat.mul_le_mul_left _ hbal
      _ ≤ 2 * (L * (Nat.sqrt M + 1)) + 2 * (L * 2 ^ ((h + 1) / 2)) := by
          apply Nat.add_le_add_right
          have : L * (2 * Nat.sqrt M) ≤ 2 * (L * Nat.sqrt M) := by
            apply le_of_eq
            ring
          calc L * (2 * Nat.sqrt M) = 2 * (L * Nat.sqrt M) := by ring
            _ ≤ 2 * (L * (Nat.sqrt M + 1)) := by
                apply Nat.mul_le_mul_left
                apply Nat.mul_le_mul_left
                omega
    -- (the +2·L·2^((h+1)/2) slop is summed via the staircase below)
  calc (∑ h ∈ range (D + 1),
        (2 ^ h * (L / 2 ^ (h / 2))) * (Nat.sqrt (M / 2 ^ h) + 1))
      ≤ ∑ h ∈ range (D + 1),
        (2 * (L * (Nat.sqrt M + 1)) + 2 * (L * 2 ^ ((h + 1) / 2))) :=
        Finset.sum_le_sum hterm
    _ = (D + 1) * (2 * (L * (Nat.sqrt M + 1))) +
        2 * (L * ∑ h ∈ range (D + 1), 2 ^ ((h + 1) / 2)) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
          smul_eq_mul, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ (D + 1) * (2 * (L * (Nat.sqrt M + 1))) +
        2 * (L * 2 ^ ((D + 1) / 2 + 2)) := by
        apply Nat.add_le_add_left
        apply Nat.mul_le_mul_left
        exact Nat.mul_le_mul_left _ (staircase_le (D + 1))
    _ ≤ (2 * (D + 1) + 64) * (L * (Nat.sqrt M + 1)) := by
        have hpow : (2:ℕ) ^ ((D + 1) / 2 + 2) ≤ 32 * (Nat.sqrt M + 1) := by
          have h6 : (2:ℕ) ^ ((D + 1) / 2 + 2) = 2 ^ ((D + 1) / 2) * 4 := by
            rw [pow_add]
            norm_num
          have h7 : (2:ℕ) ^ ((D + 1) / 2) ≤ 2 ^ (D / 2 + 1) :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
          have h8 : (2:ℕ) ^ (D / 2) ≤ Nat.sqrt (2 * M) := by
            apply Nat.le_sqrt.mpr
            calc 2 ^ (D / 2) * 2 ^ (D / 2) = 2 ^ (D / 2 + D / 2) := by
                  rw [pow_add]
              _ ≤ 2 ^ D := Nat.pow_le_pow_right (by norm_num) (by omega)
              _ ≤ 2 * M := hD
          have h9 : Nat.sqrt (2 * M) ≤ 2 * (Nat.sqrt M + 1) := by
            have h10 : 2 * M ≤ (2 * (Nat.sqrt M + 1)) * (2 * (Nat.sqrt M + 1)) := by
              have h11 := Nat.lt_succ_sqrt M
              simp only [Nat.succ_eq_add_one] at h11
              nlinarith [Nat.sqrt_le' M]
            calc Nat.sqrt (2 * M)
                ≤ Nat.sqrt ((2 * (Nat.sqrt M + 1)) * (2 * (Nat.sqrt M + 1))) :=
                  Nat.sqrt_le_sqrt h10
              _ = 2 * (Nat.sqrt M + 1) := Nat.sqrt_eq _
          calc (2:ℕ) ^ ((D + 1) / 2 + 2) = 2 ^ ((D + 1) / 2) * 4 := h6
            _ ≤ 2 ^ (D / 2 + 1) * 4 := Nat.mul_le_mul_right _ h7
            _ = 2 ^ (D / 2) * 8 := by rw [pow_succ]; ring
            _ ≤ Nat.sqrt (2 * M) * 8 := Nat.mul_le_mul_right _ h8
            _ ≤ (2 * (Nat.sqrt M + 1)) * 8 := Nat.mul_le_mul_right _ h9
            _ ≤ 32 * (Nat.sqrt M + 1) := by omega
        have e1 : (2 * (D + 1) + 64) * (L * (Nat.sqrt M + 1)) =
            (D + 1) * (2 * (L * (Nat.sqrt M + 1))) +
              64 * (L * (Nat.sqrt M + 1)) := by ring
        have e2 : 2 * (L * 2 ^ ((D + 1) / 2 + 2)) ≤
            64 * (L * (Nat.sqrt M + 1)) := by
          calc 2 * (L * 2 ^ ((D + 1) / 2 + 2))
              ≤ 2 * (L * (32 * (Nat.sqrt M + 1))) := by
                apply Nat.mul_le_mul_left
                exact Nat.mul_le_mul_left _ hpow
            _ = 64 * (L * (Nat.sqrt M + 1)) := by ring
        omega

/-! ### The amortized-cache ledger (branch `beyond-n43`)

Distinct query positions at a node never exceed its array length, so
per-(node, position) alias caches amortize the rectangle enumeration.
The cache build cost summed over a class tree is the new, ε-free mode:
every level costs at most `L·M/2^{h/2}`, hence `O(L·M)` in total. -/
theorem cache_ledger (L M D : ℕ) :
    (∑ h ∈ range (D + 1), 2 ^ h * ((L / 2 ^ (h / 2)) * (M / 2 ^ h))) ≤
      4 * (L * M) := by
  have hterm : ∀ h ∈ range (D + 1),
      2 ^ h * ((L / 2 ^ (h / 2)) * (M / 2 ^ h)) ≤ (L * M) / 2 ^ (h / 2) := by
    intro h _
    have h1 : (L / 2 ^ (h / 2)) * ((M / 2 ^ h) * 2 ^ h) ≤
        (L / 2 ^ (h / 2)) * M := by
      apply Nat.mul_le_mul_left
      rw [mul_comm]
      exact Nat.mul_div_le M (2 ^ h)
    have h2 : (L / 2 ^ (h / 2)) * M ≤ (L * M) / 2 ^ (h / 2) := by
      rw [Nat.le_div_iff_mul_le (by positivity)]
      calc L / 2 ^ (h / 2) * M * 2 ^ (h / 2)
          = (L / 2 ^ (h / 2) * 2 ^ (h / 2)) * M := by ring
        _ ≤ L * M := Nat.mul_le_mul_right _ (Nat.div_mul_le_self _ _)
    calc 2 ^ h * ((L / 2 ^ (h / 2)) * (M / 2 ^ h))
        = (L / 2 ^ (h / 2)) * ((M / 2 ^ h) * 2 ^ h) := by ring
      _ ≤ (L / 2 ^ (h / 2)) * M := h1
      _ ≤ (L * M) / 2 ^ (h / 2) := h2
  calc (∑ h ∈ range (D + 1), 2 ^ h * ((L / 2 ^ (h / 2)) * (M / 2 ^ h)))
      ≤ ∑ h ∈ range (D + 1), (L * M) / 2 ^ (h / 2) :=
        Finset.sum_le_sum hterm
    _ ≤ 4 * (L * M) := geom_half_root (D + 1) (L * M)

/-- The cache-mode collapse: against the rebuild mode `n²E/ℓ`, the ε-free
mode `nℓ` collapses to `n^{1.5}·√E` - squared form `min² ≤ n³·E`. -/
theorem cache_collapse (n ℓ E : ℕ) :
    (min ((n * n * E) / ℓ) (n * ℓ)) ^ 2 ≤ n ^ 3 * E := by
  have h1 : (min ((n * n * E) / ℓ) (n * ℓ)) ^ 2 ≤
      ((n * n * E) / ℓ) * (n * ℓ) := by
    rw [pow_two]
    exact Nat.mul_le_mul (min_le_left _ _) (min_le_right _ _)
  calc (min ((n * n * E) / ℓ) (n * ℓ)) ^ 2
      ≤ ((n * n * E) / ℓ) * (n * ℓ) := h1
    _ = ((n * n * E) / ℓ * ℓ) * n := by ring
    _ ≤ (n * n * E) * n := by
        apply Nat.mul_le_mul_right
        exact Nat.div_mul_le_self _ _
    _ = n ^ 3 * E := by ring

/-- The sharpened cache mode: a build at `(u, s)` enumerates at most
`min(M_u, L_u)` rectangles (a level occupies at least one array cell), so
each tree level costs at most `2L²` and the whole tree `Õ(L²)`. -/
theorem cache_ledger2 (L M D : ℕ) :
    (∑ h ∈ range (D + 1),
      2 ^ h * ((L / 2 ^ (h / 2)) * min (M / 2 ^ h) (L / 2 ^ (h / 2)))) ≤
      2 * (D + 1) * (L * L) := by
  have hterm : ∀ h ∈ range (D + 1),
      2 ^ h * ((L / 2 ^ (h / 2)) * min (M / 2 ^ h) (L / 2 ^ (h / 2))) ≤
        2 * (L * L) := by
    intro h _
    have h1 : (2:ℕ) ^ h ≤ 2 * (2 ^ (h / 2) * 2 ^ (h / 2)) := by
      calc (2:ℕ) ^ h ≤ 2 ^ (h / 2 + h / 2 + 1) :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 2 * (2 ^ (h / 2) * 2 ^ (h / 2)) := by
            rw [pow_succ, pow_add]
            ring
    have h2 : (L / 2 ^ (h / 2)) * min (M / 2 ^ h) (L / 2 ^ (h / 2)) ≤
        (L / 2 ^ (h / 2)) * (L / 2 ^ (h / 2)) :=
      Nat.mul_le_mul_left _ (min_le_right _ _)
    calc 2 ^ h * ((L / 2 ^ (h / 2)) * min (M / 2 ^ h) (L / 2 ^ (h / 2)))
        ≤ (2 * (2 ^ (h / 2) * 2 ^ (h / 2))) *
            ((L / 2 ^ (h / 2)) * (L / 2 ^ (h / 2))) :=
          Nat.mul_le_mul h1 h2
      _ = 2 * ((2 ^ (h / 2) * (L / 2 ^ (h / 2))) *
            (2 ^ (h / 2) * (L / 2 ^ (h / 2)))) := by ring
      _ ≤ 2 * (L * L) := by
          apply Nat.mul_le_mul_left
          apply Nat.mul_le_mul <;>
            · rw [mul_comm]
              exact Nat.div_mul_le_self L (2 ^ (h / 2))
  calc (∑ h ∈ range (D + 1),
      2 ^ h * ((L / 2 ^ (h / 2)) * min (M / 2 ^ h) (L / 2 ^ (h / 2))))
      ≤ ∑ _h ∈ range (D + 1), 2 * (L * L) := Finset.sum_le_sum hterm
    _ = 2 * (D + 1) * (L * L) := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
        ring

/-- The sharpened collapse: against the rebuild mode `n²E/ℓ`, the ε-free
`ℓ²` mode balances at `ℓ = (n²E)^{1/3}`, i.e. the sampling work is at
most `(n⁴E²)^{1/3} = n^{4/3}·ε^{-4/3}` - cube form `min³ ≤ n⁴E²`. -/
theorem cache_collapse2 (n ℓ E : ℕ) :
    (min ((n * n * E) / ℓ) (ℓ * ℓ)) ^ 3 ≤ n ^ 4 * E ^ 2 := by
  have h1 : (min ((n * n * E) / ℓ) (ℓ * ℓ)) ^ 3 ≤
      (((n * n * E) / ℓ) * ((n * n * E) / ℓ)) * (ℓ * ℓ) := by
    have e : (min ((n * n * E) / ℓ) (ℓ * ℓ)) ^ 3 =
        ((min ((n * n * E) / ℓ) (ℓ * ℓ)) * (min ((n * n * E) / ℓ) (ℓ * ℓ))) *
          (min ((n * n * E) / ℓ) (ℓ * ℓ)) := by ring
    rw [e]
    exact Nat.mul_le_mul
      (Nat.mul_le_mul (min_le_left _ _) (min_le_left _ _)) (min_le_right _ _)
  calc (min ((n * n * E) / ℓ) (ℓ * ℓ)) ^ 3
      ≤ (((n * n * E) / ℓ) * ((n * n * E) / ℓ)) * (ℓ * ℓ) := h1
    _ = (((n * n * E) / ℓ) * ℓ) * (((n * n * E) / ℓ) * ℓ) := by ring
    _ ≤ (n * n * E) * (n * n * E) := by
        apply Nat.mul_le_mul <;> exact Nat.div_mul_le_self _ _
    _ = n ^ 4 * E ^ 2 := by ring
