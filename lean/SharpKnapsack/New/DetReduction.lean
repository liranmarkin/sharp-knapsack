/-
# The fully formal merge reduction (B4, executable form)

This file closes the last prose seam of the conditional-optimality
result: it constructs the ENCODING of a MinConv instance as actual
`SparseFun` lists and machine-checks that the output of the repo's own
verified, executable GMW pipeline - `conv` followed by `sparsify` from
the `fptas` development - determines every (upper-half) MinConv value
of the instance. Together with `ramp_minConv`/`ramp_monotone`
(DetBarriers) and the published Pareto-sum lower bound (Funke et al.,
ESA 2023) under the MinConv hypothesis, this makes the barrier B4
Lean-complete: the only remaining non-Lean ingredients are the two
citations, named as such.
-/
import SharpKnapsack.Sparsify
import SharpKnapsack.New.DetBarriers

open Finset SparseFun

/-- The encoding: breakpoint `k` at position `a k` with spread mass
`2^{w·k}`, so that index sums dominate all lower diagonals. -/
def encodeSF (a : ℕ → ℕ) (n w : ℕ) : SparseFun :=
  (List.range (n + 1)).map fun k => (a k, 2 ^ (w * k))

/-- Sums of a point mass against a kernel collapse to one term. -/
theorem sum_single_mul (p v t : ℕ) (G : ℕ → ℕ) :
    (∑ y ∈ range (t + 1), single p v y * G (t - y)) =
      if p ≤ t then v * G (t - p) else 0 := by
  by_cases h : p ≤ t
  · rw [if_pos h, Finset.sum_eq_single p]
    · simp [single]
    · intro y _ hy
      simp [single, Ne.symm hy]
    · intro hp
      exact absurd (mem_range.mpr (by omega)) hp
  · rw [if_neg h, Finset.sum_eq_zero]
    intro y hy
    have hne : p ≠ y := by
      have := mem_range.mp hy
      omega
    simp [single, hne]

/-- A singleton list evaluates to a `single`. -/
theorem eval_singleton (p v : ℕ) :
    eval [(p, v)] = single p v := by
  funext x
  rw [eval_cons, eval_nil]
  simp [single]

/-- The one-point encoding evaluates to a `single`. -/
theorem eval_encode_zero (a : ℕ → ℕ) (w : ℕ) :
    eval (encodeSF a 0 w) = single (a 0) (2 ^ (w * 0)) := by
  have h : encodeSF a 0 w = [(a 0, 2 ^ (w * 0))] := rfl
  rw [h, eval_singleton]

/-- The encoding splits one breakpoint at a time. -/
theorem encode_succ (a : ℕ → ℕ) (m w : ℕ) :
    encodeSF a (m + 1) w =
      encodeSF a m w ++ [(a (m + 1), 2 ^ (w * (m + 1)))] := by
  unfold encodeSF
  rw [List.range_succ, List.map_append]
  rfl

/-- Weighted sums against the encoding collapse to sums over its
breakpoints. -/
theorem sum_eval_encode (a : ℕ → ℕ) (w : ℕ) (G : ℕ → ℕ) :
    ∀ n t, (∑ y ∈ range (t + 1), eval (encodeSF a n w) y * G (t - y)) =
      ∑ k ∈ range (n + 1), if a k ≤ t then 2 ^ (w * k) * G (t - a k) else 0 := by
  intro n
  induction n with
  | zero =>
    intro t
    simp only [eval_encode_zero]
    rw [sum_single_mul]
    simp
  | succ m ih =>
    intro t
    have hsplit : ∀ y, eval (encodeSF a (m + 1) w) y =
        eval (encodeSF a m w) y + single (a (m + 1)) (2 ^ (w * (m + 1))) y := by
      intro y
      rw [encode_succ, eval_append, eval_singleton]
    calc (∑ y ∈ range (t + 1), eval (encodeSF a (m + 1) w) y * G (t - y))
        = (∑ y ∈ range (t + 1), (eval (encodeSF a m w) y * G (t - y) +
            single (a (m + 1)) (2 ^ (w * (m + 1))) y * G (t - y))) := by
          apply Finset.sum_congr rfl
          intro y _
          rw [hsplit y, Nat.add_mul]
      _ = (∑ y ∈ range (t + 1), eval (encodeSF a m w) y * G (t - y)) +
            (∑ y ∈ range (t + 1),
              single (a (m + 1)) (2 ^ (w * (m + 1))) y * G (t - y)) :=
          Finset.sum_add_distrib
      _ = (∑ k ∈ range (m + 1), if a k ≤ t then 2 ^ (w * k) * G (t - a k) else 0) +
            (if a (m + 1) ≤ t then 2 ^ (w * (m + 1)) * G (t - a (m + 1)) else 0) := by
          rw [ih t, sum_single_mul]
      _ = ∑ k ∈ range (m + 2), if a k ≤ t then 2 ^ (w * k) * G (t - a k) else 0 := by
          conv_rhs => rw [sum_range_succ]

/-- Cumulative of the encoding. -/
theorem prefixLe_eval_encode (a : ℕ → ℕ) (w n z : ℕ) :
    prefixLe (eval (encodeSF a n w)) z =
      ∑ k ∈ range (n + 1), if a k ≤ z then 2 ^ (w * k) else 0 := by
  rw [prefixLe]
  have h := sum_eval_encode a w (fun _ => 1) n z
  simpa using h

/-- **The merged cumulative is the pair-sum double sum**: querying the
executable convolution of the two encodings at threshold `t` counts
exactly the spread masses of index pairs whose position sum fits. -/
theorem queryLe_conv_encode (a b : ℕ → ℕ) (n w t : ℕ) :
    queryLe (conv (encodeSF a n w) (encodeSF b n w)) t =
      ∑ k ∈ range (n + 1), ∑ l ∈ range (n + 1),
        if a k + b l ≤ t then 2 ^ (w * (k + l)) else 0 := by
  rw [queryLe_spec, conv_spec, prefixLe_convFun]
  rw [sum_eval_encode a w (fun z => prefixLe (eval (encodeSF b n w)) z) n t]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : a k ≤ t
  · rw [if_pos hk, prefixLe_eval_encode, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    by_cases hl : b l ≤ t - a k
    · rw [if_pos hl, if_pos (by omega), ← pow_add]
      congr 1
      ring
    · rw [if_neg hl, if_neg (by omega), Nat.mul_zero]
  · rw [if_neg hk, Finset.sum_eq_zero]
    intro l _
    rw [if_neg (by omega)]

/-! ### ℕ-valued MinConv, frontier, and the sandwich -/

/-- ℕ-valued min-plus convolution at anti-diagonal `m` (upper half). -/
def minConvN (a b : ℕ → ℕ) (n m : ℕ) : ℕ :=
  (range (n + 1)).inf' ⟨0, mem_range.mpr (Nat.succ_pos n)⟩
    (fun k => a k + b (m - k))

/-- ℕ-valued frontier: the largest upper-half index sum whose MinConv
value fits within `t`. -/
def frontierN (a b : ℕ → ℕ) (n t : ℕ) : ℕ :=
  ((range (2 * n + 1)).filter (fun m => n ≤ m ∧ minConvN a b n m ≤ t)).sup id

/-- If diagonal `n` fits, the frontier is a genuine filter member. -/
theorem frontierN_spec (a b : ℕ → ℕ) (n t : ℕ)
    (htlo : minConvN a b n n ≤ t) :
    n ≤ frontierN a b n t ∧ frontierN a b n t ≤ 2 * n ∧
      minConvN a b n (frontierN a b n t) ≤ t := by
  have hne : ((range (2 * n + 1)).filter
      (fun m => n ≤ m ∧ minConvN a b n m ≤ t)).Nonempty := by
    exact ⟨n, by
      rw [mem_filter, mem_range]
      exact ⟨by omega, le_refl n, htlo⟩⟩
  obtain ⟨M, hM, hMsup⟩ := Finset.exists_mem_eq_sup _ hne id
  rw [mem_filter, mem_range] at hM
  have hMv : frontierN a b n t = M := hMsup
  refine ⟨?_, ?_, ?_⟩
  · rw [hMv]; exact hM.2.1
  · rw [hMv]; omega
  · rw [hMv]; exact hM.2.2

/-- Every fitting pair's diagonal is at most the frontier. -/
theorem pair_le_frontier (a b : ℕ → ℕ) (n t k l : ℕ)
    (hk : k ≤ n) (hl : l ≤ n) (hkl : a k + b l ≤ t)
    (htlo : minConvN a b n n ≤ t) :
    k + l ≤ frontierN a b n t := by
  have hfr := frontierN_spec a b n t htlo
  by_cases hm : n ≤ k + l
  · apply Finset.le_sup (f := id)
    rw [mem_filter, mem_range]
    refine ⟨by omega, hm, ?_⟩
    calc minConvN a b n (k + l)
        ≤ a k + b (k + l - k) := Finset.inf'_le _ (mem_range.mpr (by omega))
      _ = a k + b l := by rw [Nat.add_sub_cancel_left]
      _ ≤ t := hkl
  · omega

/-- **The sandwich, lower side**: the frontier's attaining pair puts
`2^{w·M}` inside the merged cumulative (needs `b` huge past `n`, so the
attaining split stays on the encoded grid). -/
theorem cum_lower (a b : ℕ → ℕ) (n w t : ℕ)
    (htlo : minConvN a b n n ≤ t)
    (hbig : ∀ l, n < l → t < b l) :
    2 ^ (w * frontierN a b n t) ≤
      queryLe (conv (encodeSF a n w) (encodeSF b n w)) t := by
  obtain ⟨hMn, hM2n, hMle⟩ := frontierN_spec a b n t htlo
  set M := frontierN a b n t with hMdef
  obtain ⟨k, hk, hkeq⟩ := Finset.exists_mem_eq_inf'
    (⟨0, mem_range.mpr (Nat.succ_pos n)⟩ :
      ((range (n + 1)).Nonempty)) (fun k => a k + b (M - k))
  have hkn : k ≤ n := by
    have := mem_range.mp hk
    omega
  have hattain : a k + b (M - k) ≤ t := by
    rw [minConvN, hkeq] at hMle
    exact hMle
  have hlk : M - k ≤ n := by
    by_contra hcon
    rw [Nat.not_le] at hcon
    have := hbig (M - k) hcon
    omega
  rw [queryLe_conv_encode]
  have hterm : 2 ^ (w * M) ≤
      ∑ l ∈ range (n + 1), if a k + b l ≤ t then 2 ^ (w * (k + l)) else 0 := by
    have hkM : k ≤ M := le_trans hkn hMn
    calc 2 ^ (w * M)
        = (if a k + b (M - k) ≤ t then 2 ^ (w * (k + (M - k))) else 0) := by
          rw [if_pos hattain]
          congr 2
          omega
      _ ≤ ∑ l ∈ range (n + 1),
            if a k + b l ≤ t then 2 ^ (w * (k + l)) else 0 := by
          apply Finset.single_le_sum (f := fun l =>
            if a k + b l ≤ t then 2 ^ (w * (k + l)) else 0)
            (fun l _ => Nat.zero_le _) (mem_range.mpr (by omega))
  calc 2 ^ (w * M)
      ≤ ∑ l ∈ range (n + 1), if a k + b l ≤ t then 2 ^ (w * (k + l)) else 0 :=
        hterm
    _ ≤ ∑ k' ∈ range (n + 1), ∑ l ∈ range (n + 1),
          if a k' + b l ≤ t then 2 ^ (w * (k' + l)) else 0 := by
        apply Finset.single_le_sum (f := fun k' =>
          ∑ l ∈ range (n + 1), if a k' + b l ≤ t then 2 ^ (w * (k' + l)) else 0)
          (fun k' _ => Nat.zero_le _) (mem_range.mpr (by omega))

/-- **The sandwich, upper side**: every contributing pair sits on a
diagonal at most the frontier, so the cumulative is at most
`(n+1)²·2^{w·M}`. -/
theorem cum_upper (a b : ℕ → ℕ) (n w t : ℕ)
    (htlo : minConvN a b n n ≤ t) :
    queryLe (conv (encodeSF a n w) (encodeSF b n w)) t ≤
      (n + 1) ^ 2 * 2 ^ (w * frontierN a b n t) := by
  rw [queryLe_conv_encode]
  set M := frontierN a b n t with hMdef
  have hbound : ∀ k ∈ range (n + 1), ∀ l ∈ range (n + 1),
      (if a k + b l ≤ t then 2 ^ (w * (k + l)) else 0) ≤ 2 ^ (w * M) := by
    intro k hk l hl
    by_cases h : a k + b l ≤ t
    · rw [if_pos h]
      apply Nat.pow_le_pow_right (by norm_num)
      apply Nat.mul_le_mul_left
      exact pair_le_frontier a b n t k l
        (by have := mem_range.mp hk; omega)
        (by have := mem_range.mp hl; omega) h htlo
    · rw [if_neg h]
      exact Nat.zero_le _
  calc (∑ k ∈ range (n + 1), ∑ l ∈ range (n + 1),
      if a k + b l ≤ t then 2 ^ (w * (k + l)) else 0)
      ≤ ∑ k ∈ range (n + 1), ∑ l ∈ range (n + 1), 2 ^ (w * M) := by
        apply Finset.sum_le_sum
        intro k hk
        exact Finset.sum_le_sum (fun l hl => hbound k hk l hl)
    _ = (n + 1) ^ 2 * 2 ^ (w * M) := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul,
          Finset.sum_const, Finset.card_range, smul_eq_mul]
        ring

/-! ### The read-off: block-logarithm recovery of the frontier -/

/-- **Exact read-off.** With spread `w` beating the pair count, the
base-2 logarithm of the merged cumulative, divided by `w`, IS the
frontier - hence the merge output determines MinConv. -/
theorem readoff_exact (a b : ℕ → ℕ) (n w t : ℕ)
    (hw : (n + 1) ^ 2 < 2 ^ w)
    (htlo : minConvN a b n n ≤ t)
    (hbig : ∀ l, n < l → t < b l) :
    Nat.log 2 (queryLe (conv (encodeSF a n w) (encodeSF b n w)) t) / w =
      frontierN a b n t := by
  set M := frontierN a b n t with hMdef
  set Q := queryLe (conv (encodeSF a n w) (encodeSF b n w)) t with hQdef
  have hlo : 2 ^ (w * M) ≤ Q := cum_lower a b n w t htlo hbig
  have hhi : Q ≤ (n + 1) ^ 2 * 2 ^ (w * M) := cum_upper a b n w t htlo
  have hQpos : Q ≠ 0 := by
    have : 0 < 2 ^ (w * M) := Nat.two_pow_pos _
    omega
  have hw0 : 0 < w := by
    by_contra hcon
    have hz : w = 0 := by omega
    rw [hz] at hw
    simp at hw
  have hlog_lo : w * M ≤ Nat.log 2 Q :=
    Nat.le_log_of_pow_le (by norm_num) hlo
  have hlog_hi : Nat.log 2 Q < w * M + w := by
    apply Nat.log_lt_of_lt_pow hQpos
    calc Q ≤ (n + 1) ^ 2 * 2 ^ (w * M) := hhi
      _ < 2 ^ w * 2 ^ (w * M) := by
          exact (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr hw
      _ = 2 ^ (w * M + w) := by
          rw [← pow_add]
          congr 1
          ring
  have h1 : M * w ≤ Nat.log 2 Q := by
    rw [Nat.mul_comm]
    exact hlog_lo
  have h2 : Nat.log 2 Q < (M + 1) * w := by
    calc Nat.log 2 Q < w * M + w := hlog_hi
      _ = (M + 1) * w := by ring
  exact Nat.div_eq_of_lt_le h1 h2

/-- The encoding is well-formed for strictly increasing positions. -/
theorem encodeSF_wf (a : ℕ → ℕ) (n w : ℕ)
    (ha : ∀ i j, i < j → j ≤ n → a i < a j) :
    WF (encodeSF a n w) := by
  constructor
  · unfold encodeSF
    rw [List.pairwise_map]
    have h := List.pairwise_lt_range (n := n + 1)
    apply List.Pairwise.imp_of_mem _ h
    intro i j hi hj hij
    exact ha i j hij (by
      have := List.mem_range.mp hj
      omega)
  · intro p hp
    unfold encodeSF at hp
    rw [List.mem_map] at hp
    obtain ⟨k, _, hk⟩ := hp
    rw [← hk]
    exact Nat.two_pow_pos _

/-- **Sparsified read-off - the full pipeline.** The output of the
repo's executable, VERIFIED GMW merge (`conv` then `sparsify`, exactly
as in the `fptas` development) still determines the frontier: the
factor-2 sparsification slack is absorbed by one extra bit of spread.
This is the reduction B4 in executable form. -/
theorem readoff_sparsified (a b : ℕ → ℕ) (n w t : ℕ)
    (hw : 2 * (n + 1) ^ 2 < 2 ^ w)
    (ha : ∀ i j, i < j → j ≤ n → a i < a j)
    (hb : ∀ i j, i < j → j ≤ n → b i < b j)
    (htlo : minConvN a b n n ≤ t)
    (hbig : ∀ l, n < l → t < b l) :
    Nat.log 2 (queryLe (sparsify 1 (conv (encodeSF a n w) (encodeSF b n w))) t)
      / w = frontierN a b n t := by
  set M := frontierN a b n t with hMdef
  set C := conv (encodeSF a n w) (encodeSF b n w) with hCdef
  have hWF : WF C := conv_wf (encodeSF_wf a n w ha) (encodeSF_wf b n w hb)
  obtain ⟨happrox, _⟩ := sparsify_spec 1 (by norm_num) hWF
  set Q := queryLe (sparsify 1 C) t with hQdef
  have hQ1 : queryLe C t ≤ Q := by
    rw [hQdef, queryLe_spec, queryLe_spec]
    exact happrox.le t
  have hQ2 : Q ≤ 2 * queryLe C t := by
    have hge := happrox.ge t
    rw [hQdef, queryLe_spec, queryLe_spec]
    have h2 : ((prefixLe (eval (sparsify 1 C)) t : ℕ) : ℚ) ≤
        2 * (prefixLe (eval C) t : ℕ) := by
      calc ((prefixLe (eval (sparsify 1 C)) t : ℕ) : ℚ)
          ≤ (1 + 1) * (prefixLe (eval C) t : ℕ) := hge
        _ = 2 * (prefixLe (eval C) t : ℕ) := by norm_num
    exact_mod_cast h2
  have hlo : 2 ^ (w * M) ≤ Q :=
    le_trans (cum_lower a b n w t htlo hbig) hQ1
  have hhi : Q ≤ 2 * ((n + 1) ^ 2 * 2 ^ (w * M)) := by
    calc Q ≤ 2 * queryLe C t := hQ2
      _ ≤ 2 * ((n + 1) ^ 2 * 2 ^ (w * M)) :=
          Nat.mul_le_mul_left _ (cum_upper a b n w t htlo)
  have hQpos : Q ≠ 0 := by
    have : 0 < 2 ^ (w * M) := Nat.two_pow_pos _
    omega
  have hw0 : 0 < w := by
    by_contra hcon
    have hz : w = 0 := by omega
    rw [hz] at hw
    simp at hw
  have hlog_lo : w * M ≤ Nat.log 2 Q :=
    Nat.le_log_of_pow_le (by norm_num) hlo
  have hlog_hi : Nat.log 2 Q < w * M + w := by
    apply Nat.log_lt_of_lt_pow hQpos
    calc Q ≤ 2 * ((n + 1) ^ 2 * 2 ^ (w * M)) := hhi
      _ = (2 * (n + 1) ^ 2) * 2 ^ (w * M) := by ring
      _ < 2 ^ w * 2 ^ (w * M) := by
          exact (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr hw
      _ = 2 ^ (w * M + w) := by
          rw [← pow_add]
          congr 1
          ring
  have h1 : M * w ≤ Nat.log 2 Q := by
    rw [Nat.mul_comm]
    exact hlog_lo
  have h2 : Nat.log 2 Q < (M + 1) * w := by
    calc Nat.log 2 Q < w * M + w := hlog_hi
      _ = (M + 1) * w := by ring
  exact Nat.div_eq_of_lt_le h1 h2
