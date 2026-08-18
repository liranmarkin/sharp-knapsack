/-
# Stage D.3: the popular weight class (Feng-Jin Lemma 3.1)

Among any item collection carrying weight ≥ T/2 with individual weights in
(0, T], some dyadic weight class (T/ℓ, 2T/ℓ] (with ℓ = 2^k ∈ [2, 8n])
contains at least ℓ/(8·⌈log₂ 4n⌉) items. This is the structural fact that
fixes the popularity parameter ℓ of the whole algorithm; conditions are
stated multiplicatively (`T < W j · ℓ`) to avoid ℕ-division issues.
-/
import SharpKnapsack.SamplerReduction

open Finset

/-- Each item of weight in (0, T] belongs to the dyadic class
`k = log₂(T/w) + 1`, in the multiplicative sense `T < w·2^k ≤ 2T`. -/
theorem dyadic_class_spec (T w : ℕ) (hw : 0 < w) (hwT : w ≤ T) :
    T < w * 2 ^ (Nat.log 2 (T / w) + 1) ∧
      w * 2 ^ (Nat.log 2 (T / w) + 1) ≤ 2 * T := by
  have hdiv : 0 < T / w := Nat.div_pos hwT hw
  constructor
  · have h1 : T / w < 2 ^ (Nat.log 2 (T / w) + 1) :=
      Nat.lt_pow_succ_log_self (by norm_num) _
    have hdm := Nat.div_add_mod T w
    have hmod : T % w < w := Nat.mod_lt T hw
    calc T < w * (T / w) + w := by omega
      _ = w * (T / w + 1) := by ring
      _ ≤ w * 2 ^ (Nat.log 2 (T / w) + 1) :=
          Nat.mul_le_mul_left _ (by omega)
  · have h3 : 2 ^ Nat.log 2 (T / w) ≤ T / w :=
      Nat.pow_log_le_self 2 (by omega)
    calc w * 2 ^ (Nat.log 2 (T / w) + 1)
        = 2 * (w * 2 ^ Nat.log 2 (T / w)) := by rw [pow_succ]; ring
      _ ≤ 2 * (w * (T / w)) := by
          apply Nat.mul_le_mul_left
          exact Nat.mul_le_mul_left _ h3
      _ ≤ 2 * T := by
          apply Nat.mul_le_mul_left
          rw [mul_comm]
          exact Nat.div_mul_le_self T w
/-- **The popular weight class exists** (Feng-Jin Lemma 3.1): if a set `I`
of at most `n` items with weights in `(0, T]` carries weight ≥ T/2, then
some dyadic `ℓ = 2^k ∈ [2, 8n]` has more than `ℓ/(8·⌈log₂ 4n⌉)` items of
`I` in the class `(T/ℓ, 2T/ℓ]`. -/
theorem popular_class (n T : ℕ) (W : ℕ → ℕ) (I : Finset ℕ)
    (hI : I ⊆ range n) (hn : 0 < n) (hT : 0 < T)
    (hcap : ∀ j ∈ I, 0 < W j ∧ W j ≤ T)
    (hlow : T ≤ 2 * ∑ j ∈ I, W j) :
    ∃ ℓ : ℕ, 2 ≤ ℓ ∧ ℓ ≤ 8 * n ∧
      ℓ ≤ 8 * Nat.clog 2 (4 * n) *
        (I.filter (fun j => T < W j * ℓ ∧ W j * ℓ ≤ 2 * T)).card := by
  set L := Nat.clog 2 (4 * n) with hL
  have hLpos : 0 < L := by
    rw [hL]
    exact Nat.clog_pos (by norm_num) (by omega)
  have h2L : 4 * n ≤ 2 ^ L := Nat.le_pow_clog (by norm_num) _
  -- the heavy items G carry at least T/4
  set G := I.filter (fun j => T < W j * 2 ^ L) with hG
  have hGweight : T ≤ 4 * ∑ j ∈ G, W j := by
    have hsplit : (∑ j ∈ I \ G, W j) + ∑ j ∈ G, W j = ∑ j ∈ I, W j :=
      Finset.sum_sdiff (Finset.filter_subset _ _)
    have h1 : (∑ j ∈ I \ G, W j) * 2 ^ L ≤ (I \ G).card * T := by
      rw [Finset.sum_mul]
      calc (∑ j ∈ I \ G, W j * 2 ^ L) ≤ ∑ _j ∈ I \ G, T := by
            apply Finset.sum_le_sum
            intro j hj
            rw [Finset.mem_sdiff, hG, Finset.mem_filter] at hj
            have h2 := hj.2
            push Not at h2
            exact h2 hj.1
        _ = (I \ G).card * T := by rw [Finset.sum_const, smul_eq_mul]
    have h2 : (I \ G).card ≤ n := by
      calc (I \ G).card ≤ I.card := Finset.card_le_card Finset.sdiff_subset
        _ ≤ (range n).card := Finset.card_le_card hI
        _ = n := Finset.card_range n
    have hlight : 4 * n * ∑ j ∈ I \ G, W j ≤ n * T := by
      calc 4 * n * ∑ j ∈ I \ G, W j = (∑ j ∈ I \ G, W j) * (4 * n) := by ring
        _ ≤ (∑ j ∈ I \ G, W j) * 2 ^ L := Nat.mul_le_mul_left _ h2L
        _ ≤ (I \ G).card * T := h1
        _ ≤ n * T := Nat.mul_le_mul_right _ h2
    have h3 : 4 * ∑ j ∈ I \ G, W j ≤ T := by
      by_contra hcon
      push Not at hcon
      have h4 : n * T < n * (4 * ∑ j ∈ I \ G, W j) :=
        (Nat.mul_lt_mul_left (by omega)).mpr hcon
      have h5 : n * (4 * ∑ j ∈ I \ G, W j) = 4 * n * ∑ j ∈ I \ G, W j := by ring
      omega
    omega
  -- fiberwise decomposition over the dyadic classes
  set assign := fun j => Nat.log 2 (T / W j) + 1 with hassign
  have hmaps : ∀ j ∈ G, assign j ∈ Finset.Icc 1 L := by
    intro j hj
    rw [hG, Finset.mem_filter] at hj
    obtain ⟨hjI, hjW⟩ := hj
    obtain ⟨hw0, hwT⟩ := hcap j hjI
    have hdivlt : T / W j < 2 ^ L := by
      rw [Nat.div_lt_iff_lt_mul hw0]
      calc T < W j * 2 ^ L := hjW
        _ = 2 ^ L * W j := Nat.mul_comm _ _
    have hlog : Nat.log 2 (T / W j) < L := by
      rcases Nat.eq_zero_or_pos (T / W j) with h0 | hpos
      · rw [h0]
        simpa using hLpos
      · exact Nat.log_lt_of_lt_pow (by omega) hdivlt
    have heq : assign j = Nat.log 2 (T / W j) + 1 := rfl
    rw [Finset.mem_Icc]
    omega
  have hfiber : (∑ k ∈ Finset.Icc 1 L,
      ∑ j ∈ G.filter (fun j => assign j = k), W j) = ∑ j ∈ G, W j :=
    Finset.sum_fiberwise_of_maps_to hmaps _
  -- pigeonhole: some class carries weight ≥ T/(4L)
  have hcount : (Finset.Icc 1 L).card = L := by
    rw [Nat.card_Icc]
    omega
  have hpigeon : ∃ k ∈ Finset.Icc 1 L,
      T ≤ 4 * L * ∑ j ∈ G.filter (fun j => assign j = k), W j := by
    by_contra hcon
    push Not at hcon
    have hstrict : ∀ k ∈ Finset.Icc 1 L,
        4 * L * (∑ j ∈ G.filter (fun j => assign j = k), W j) + 1 ≤ T := by
      intro k hk
      have := hcon k hk
      omega
    have hexp : (∑ k ∈ Finset.Icc 1 L,
        (4 * L * (∑ j ∈ G.filter (fun j => assign j = k), W j) + 1)) =
        4 * L * (∑ j ∈ G, W j) + L := by
      rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one, hcount,
        ← Finset.mul_sum, hfiber]
    have hsum : 4 * L * (∑ j ∈ G, W j) + L ≤ L * T := by
      rw [← hexp]
      calc (∑ k ∈ Finset.Icc 1 L,
          (4 * L * (∑ j ∈ G.filter (fun j => assign j = k), W j) + 1))
          ≤ ∑ _k ∈ Finset.Icc 1 L, T := Finset.sum_le_sum hstrict
        _ = L * T := by rw [Finset.sum_const, smul_eq_mul, hcount]
    have h5 := Nat.mul_le_mul_left L hGweight
    have h6 : L * (4 * ∑ j ∈ G, W j) = 4 * L * ∑ j ∈ G, W j := by ring
    omega
  obtain ⟨k, hkmem, hkw⟩ := hpigeon
  rw [Finset.mem_Icc] at hkmem
  refine ⟨2 ^ k, ?_, ?_, ?_⟩
  · calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hkmem.1
  · have hlt := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (by omega : 1 < 4 * n)
    rw [← hL] at hlt
    have h7 : (2:ℕ) ^ k ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hkmem.2
    calc (2:ℕ) ^ k ≤ 2 ^ L := h7
      _ = 2 * 2 ^ (L - 1) := by
          conv_lhs => rw [show L = (L - 1) + 1 from by omega]
          rw [pow_succ']
      _ ≤ 2 * (4 * n) := Nat.mul_le_mul_left _ (le_of_lt hlt)
      _ = 8 * n := by ring
  · -- the class is inside the target filter, and its weight pins its size
    set Fk := I.filter (fun j => T < W j * 2 ^ k ∧ W j * 2 ^ k ≤ 2 * T) with hFk
    have hclass_sub : G.filter (fun j => assign j = k) ⊆ Fk := by
      intro j hj
      rw [Finset.mem_filter] at hj
      obtain ⟨hjG, hjk⟩ := hj
      rw [hG, Finset.mem_filter] at hjG
      obtain ⟨hjI, -⟩ := hjG
      obtain ⟨hw0, hwT⟩ := hcap j hjI
      have hspec := dyadic_class_spec T (W j) hw0 hwT
      rw [hassign] at hjk
      rw [hFk, Finset.mem_filter, ← hjk]
      exact ⟨hjI, hspec.1, hspec.2⟩
    have hcw_ub : (∑ j ∈ G.filter (fun j => assign j = k), W j) * 2 ^ k ≤
        Fk.card * (2 * T) := by
      rw [Finset.sum_mul]
      calc (∑ j ∈ G.filter (fun j => assign j = k), W j * 2 ^ k)
          ≤ ∑ _j ∈ G.filter (fun j => assign j = k), 2 * T := by
            apply Finset.sum_le_sum
            intro j hj
            have := hclass_sub hj
            rw [hFk, Finset.mem_filter] at this
            exact this.2.2
        _ = (G.filter (fun j => assign j = k)).card * (2 * T) := by
            rw [Finset.sum_const, smul_eq_mul]
        _ ≤ Fk.card * (2 * T) :=
            Nat.mul_le_mul_right _ (Finset.card_le_card hclass_sub)
    have hfinal : T * 2 ^ k ≤ (8 * L * Fk.card) * T := by
      calc T * 2 ^ k
          ≤ (4 * L * ∑ j ∈ G.filter (fun j => assign j = k), W j) * 2 ^ k :=
            Nat.mul_le_mul_right _ hkw
        _ = 4 * L * ((∑ j ∈ G.filter (fun j => assign j = k), W j) * 2 ^ k) := by
            ring
        _ ≤ 4 * L * (Fk.card * (2 * T)) := Nat.mul_le_mul_left _ hcw_ub
        _ = (8 * L * Fk.card) * T := by ring
    have h8 : 2 ^ k * T ≤ (8 * L * Fk.card) * T := by
      calc 2 ^ k * T = T * 2 ^ k := Nat.mul_comm _ _
        _ ≤ (8 * L * Fk.card) * T := hfinal
    exact Nat.le_of_mul_le_mul_right h8 hT
