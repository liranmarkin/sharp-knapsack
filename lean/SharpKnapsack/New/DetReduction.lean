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

/-! ### Padding: every diagonal is an upper-half diagonal

Prepending `n` huge (distinct) entries to both sequences places every
original anti-diagonal `d ∈ [0, 2n]` at the padded upper-half diagonal
`2n + d`. The ramp (`ramp_monotone`) then makes the padded sequences
strictly increasing, so the sparsified read-off applies verbatim and
the merge output determines the ENTIRE MinConv, not just its upper
half. -/

/-- Bottom-padding with `n` distinct huge entries. -/
def padSeq (a : ℕ → ℕ) (n H : ℕ) : ℕ → ℕ :=
  fun k => if k < n then H + k else a (k - n)

/-- Every genuine pair of the original instance bounds the padded
upper-half MinConv from above. -/
theorem minConv_pad_le (a b : ℕ → ℕ) (n d H k : ℕ)
    (hk : k ≤ d) (hkn : k ≤ n) (hdk : d - k ≤ n) :
    minConvN (padSeq a n H) (padSeq b n H) (2 * n) (2 * n + d) ≤
      a k + b (d - k) := by
  have hmem : n + k ∈ range (2 * n + 1) := mem_range.mpr (by omega)
  calc minConvN (padSeq a n H) (padSeq b n H) (2 * n) (2 * n + d)
      ≤ padSeq a n H (n + k) + padSeq b n H (2 * n + d - (n + k)) :=
        Finset.inf'_le _ hmem
    _ = a k + b (d - k) := by
        unfold padSeq
        rw [if_neg (by omega), if_neg (by omega)]
        congr 2
        · omega
        · omega

/-- The padded upper-half MinConv is attained at a genuine pair,
provided `H` dominates all genuine values. -/
theorem minConv_pad_attained (a b : ℕ → ℕ) (n d H : ℕ) (hd : d ≤ 2 * n)
    (hH : ∀ k l, k ≤ n → l ≤ n → a k + b l < H)
    (hHb : ∀ l, n < l → H ≤ b l) :
    ∃ k, k ≤ d ∧ k ≤ n ∧ d - k ≤ n ∧ d ≤ k + n ∧
      minConvN (padSeq a n H) (padSeq b n H) (2 * n) (2 * n + d) =
        a k + b (d - k) := by
  obtain ⟨k', hk', hkeq⟩ := Finset.exists_mem_eq_inf'
    (⟨0, mem_range.mpr (Nat.succ_pos (2 * n))⟩ :
      ((range (2 * n + 1)).Nonempty))
    (fun k => padSeq a n H k + padSeq b n H (2 * n + d - k))
  have hk2n : k' ≤ 2 * n := by
    have := mem_range.mp hk'
    omega
  -- a genuine witness exists, so the min is below H
  have hgen : ∃ kg, kg ≤ d ∧ kg ≤ n ∧ d - kg ≤ n := by
    rcases Nat.le_total d n with hdn | hnd
    · exact ⟨d, le_refl d, hdn, by omega⟩
    · exact ⟨n, hnd, le_refl n, by omega⟩
  obtain ⟨kg, hkg1, hkg2, hkg3⟩ := hgen
  have hlt : minConvN (padSeq a n H) (padSeq b n H) (2 * n) (2 * n + d) < H := by
    calc minConvN (padSeq a n H) (padSeq b n H) (2 * n) (2 * n + d)
        ≤ a kg + b (d - kg) := minConv_pad_le a b n d H kg hkg1 hkg2 hkg3
      _ < H := hH kg (d - kg) hkg2 hkg3
  -- the attaining split point cannot touch a pad entry
  have hnotpad_a : ¬ k' < n := by
    intro hcon
    have hpad : H ≤ padSeq a n H k' := by
      unfold padSeq
      rw [if_pos hcon]
      omega
    have hsum : H ≤ padSeq a n H k' + padSeq b n H (2 * n + d - k') :=
      le_trans hpad (Nat.le_add_right _ _)
    rw [minConvN, hkeq] at hlt
    exact absurd hlt (not_lt.mpr hsum)
  have hnotpad_b : ¬ 2 * n + d - k' < n := by
    intro hcon
    have hpad : H ≤ padSeq b n H (2 * n + d - k') := by
      unfold padSeq
      rw [if_pos hcon]
      omega
    have hsum : H ≤ padSeq a n H k' + padSeq b n H (2 * n + d - k') :=
      le_trans hpad (Nat.le_add_left _ _)
    rw [minConvN, hkeq] at hlt
    exact absurd hlt (not_lt.mpr hsum)
  have hnotpad_c : ¬ 2 * n < 2 * n + d - k' := by
    intro hcon
    have hpad : H ≤ padSeq b n H (2 * n + d - k') := by
      unfold padSeq
      rw [if_neg (by omega)]
      exact hHb _ (by omega)
    have hsum : H ≤ padSeq a n H k' + padSeq b n H (2 * n + d - k') :=
      le_trans hpad (Nat.le_add_left _ _)
    rw [minConvN, hkeq] at hlt
    exact absurd hlt (not_lt.mpr hsum)
  refine ⟨k' - n, by omega, by omega, by omega, by omega, ?_⟩
  rw [minConvN, hkeq]
  show padSeq a n H k' + padSeq b n H (2 * n + d - k') = _
  unfold padSeq
  rw [if_neg (by omega), if_neg (by omega)]
  congr 2 <;> omega

/-! ### ℕ-side ramp and frontier bridge -/

/-- ℕ-ramp. -/
def rampN (a : ℕ → ℕ) (R : ℕ) : ℕ → ℕ := fun k => a k + R * k

/-- The ℕ-ramp shifts every upper-half anti-diagonal uniformly. -/
theorem rampN_minConv (a b : ℕ → ℕ) (R n m : ℕ) (hm : n ≤ m) :
    minConvN (rampN a R) (rampN b R) n m = minConvN a b n m + R * m := by
  have hne : (range (n + 1)).Nonempty := ⟨0, mem_range.mpr (Nat.succ_pos n)⟩
  have h1 : minConvN (rampN a R) (rampN b R) n m =
      (range (n + 1)).inf' hne (fun k => (a k + b (m - k)) + R * m) := by
    show (range (n + 1)).inf' _ (fun k => rampN a R k + rampN b R (m - k)) = _
    apply Finset.inf'_congr _ rfl
    intro k hk
    have hkn : k ≤ n := by
      have := mem_range.mp hk
      omega
    unfold rampN
    have hkm : k ≤ m := le_trans hkn hm
    have : R * k + R * (m - k) = R * m := by
      rw [← Nat.mul_add]
      congr 1
      omega
    omega
  rw [h1]
  apply le_antisymm
  · obtain ⟨k, hk, hkeq⟩ := Finset.exists_mem_eq_inf' hne
      (fun k => a k + b (m - k))
    have hmc : minConvN a b n m = a k + b (m - k) := hkeq
    calc (range (n + 1)).inf' hne (fun k => (a k + b (m - k)) + R * m)
        ≤ (a k + b (m - k)) + R * m := Finset.inf'_le _ hk
      _ = minConvN a b n m + R * m := by rw [hmc]
  · apply Finset.le_inf'
    intro k hk
    have h2 : minConvN a b n m ≤ a k + b (m - k) := Finset.inf'_le _ hk
    omega

/-- ℕ-frontier bridge: MinConv threshold membership reads off the
frontier, given upper-half monotonicity. -/
theorem frontierN_readoff (a b : ℕ → ℕ) (n m t : ℕ)
    (hn : 1 ≤ n) (hm : n ≤ m) (hm2 : m ≤ 2 * n)
    (hmono : ∀ m₁ m₂, n ≤ m₁ → m₁ ≤ m₂ → m₂ ≤ 2 * n →
      minConvN a b n m₁ ≤ minConvN a b n m₂) :
    minConvN a b n m ≤ t ↔ m ≤ frontierN a b n t := by
  constructor
  · intro h
    apply Finset.le_sup (f := id)
    rw [mem_filter, mem_range]
    exact ⟨by omega, hm, h⟩
  · intro h
    by_cases hne : ((range (2 * n + 1)).filter
        (fun m' => n ≤ m' ∧ minConvN a b n m' ≤ t)).Nonempty
    · obtain ⟨m', hm', hmax⟩ := Finset.exists_mem_eq_sup _ hne id
      have hval : frontierN a b n t = m' := hmax
      rw [hval] at h
      rw [mem_filter, mem_range] at hm'
      calc minConvN a b n m ≤ minConvN a b n m' := by
            rcases Nat.le_total m m' with hle | hge
            · exact hmono m m' hm hle (by omega)
            · have : m = m' := by omega
              rw [this]
        _ ≤ t := hm'.2.2
    · exfalso
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [frontierN, hne] at h
      simp at h
      omega

/-- Monotone second operand gives upper-half monotone MinConv (ℕ). -/
theorem minConvN_mono (a b : ℕ → ℕ) (n : ℕ)
    (hb : ∀ i j, i ≤ j → b i ≤ b j) (m₁ m₂ : ℕ) (h : m₁ ≤ m₂) :
    minConvN a b n m₁ ≤ minConvN a b n m₂ := by
  apply Finset.le_inf'
  intro k hk
  calc minConvN a b n m₁ ≤ a k + b (m₁ - k) := Finset.inf'_le _ hk
    _ ≤ a k + b (m₂ - k) := by
        have := hb (m₁ - k) (m₂ - k) (by omega)
        omega

/-! ### B2 core: a multiplicative approximation of the exact-weight
count decides Subset-Sum -/

/-- Number of subsets hitting weight `C` exactly. -/
def exactWeightCount (n : ℕ) (W : ℕ → ℕ) (C : ℕ) : ℕ :=
  ((Finset.range n).powerset.filter (fun X => ∑ i ∈ X, W i = C)).card

/-- **B2 core.** ANY multiplicative approximation of the exact-weight
count - however coarse - decides Subset-Sum. Hence no FPTAS (or any
poly-factor approximation) exists for window-isolated counting unless
P = NP; cumulative counting from zero is forced. -/
theorem approx_decides_subset_sum (n : ℕ) (W : ℕ → ℕ) (C A K : ℕ)
    (hlo : exactWeightCount n W C ≤ A)
    (hhi : A ≤ K * exactWeightCount n W C) :
    0 < A ↔ ∃ X ⊆ Finset.range n, ∑ i ∈ X, W i = C := by
  constructor
  · intro hA
    have hpos : 0 < exactWeightCount n W C := by
      by_contra h
      have hz : exactWeightCount n W C = 0 := by omega
      rw [hz, Nat.mul_zero] at hhi
      omega
    rw [exactWeightCount, Finset.card_pos] at hpos
    obtain ⟨X, hX⟩ := hpos
    rw [Finset.mem_filter, Finset.mem_powerset] at hX
    exact ⟨X, hX.1, hX.2⟩
  · rintro ⟨X, hX1, hX2⟩
    have hpos : 0 < exactWeightCount n W C := by
      rw [exactWeightCount, Finset.card_pos]
      refine ⟨X, ?_⟩
      rw [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨hX1, hX2⟩
    omega

/-! ### B3 witness: the arithmetic-geometric family saturates the band -/

/-- **B3 witness, machine-checked.** For arithmetic positions with
geometric masses, EVERY pair is in-band: the full pair-sum cumulative
at any pair's position stays within `(n+1)² ≤ 2^w` of that pair's own
diagonal mass. This is the family on which the in-band sweep provably
degenerates to Θ(s²). -/
theorem witness_all_inband (c n w : ℕ) (hc : 0 < c)
    (hw : (n + 1) ^ 2 ≤ 2 ^ w) (j l : ℕ) (_hj : j ≤ n) (_hl : l ≤ n) :
    (∑ k ∈ range (n + 1), ∑ m ∈ range (n + 1),
      if c * k + c * m ≤ c * j + c * l then 2 ^ (k + m) else 0) ≤
      2 ^ (j + l + w) := by
  have hbound : ∀ k ∈ range (n + 1), ∀ m ∈ range (n + 1),
      (if c * k + c * m ≤ c * j + c * l then 2 ^ (k + m) else 0) ≤
        2 ^ (j + l) := by
    intro k _ m _
    by_cases h : c * k + c * m ≤ c * j + c * l
    · rw [if_pos h]
      apply Nat.pow_le_pow_right (by norm_num)
      have h1 : c * (k + m) ≤ c * (j + l) := by
        rw [Nat.mul_add, Nat.mul_add]
        omega
      exact Nat.le_of_mul_le_mul_left h1 hc
    · rw [if_neg h]
      exact Nat.zero_le _
  calc (∑ k ∈ range (n + 1), ∑ m ∈ range (n + 1),
      if c * k + c * m ≤ c * j + c * l then 2 ^ (k + m) else 0)
      ≤ ∑ k ∈ range (n + 1), ∑ m ∈ range (n + 1), 2 ^ (j + l) := by
        apply Finset.sum_le_sum
        intro k hk
        exact Finset.sum_le_sum (fun m hm => hbound k hk m hm)
    _ = (n + 1) ^ 2 * 2 ^ (j + l) := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul,
          Finset.sum_const, Finset.card_range, smul_eq_mul]
        ring
    _ ≤ 2 ^ w * 2 ^ (j + l) := Nat.mul_le_mul_right _ hw
    _ = 2 ^ (j + l + w) := by
        rw [← pow_add]
        congr 1
        ring

/-! ### The composed reduction: one executable statement -/

/-- Dominance height. -/
def detH (B : ℕ) : ℕ := 2 * B + 1

/-- Ramp slope: beats every possible drop of the padded sequence. -/
def detR (B n : ℕ) : ℕ := detH B + n + 1

/-- Domain extension: huge beyond `n` (so out-of-range splits never
attain). -/
def detExt (b : ℕ → ℕ) (n t : ℕ) : ℕ → ℕ :=
  fun l => if l ≤ n then b l else t + 1

/-- The fully processed first operand: pad, then ramp. -/
def detA (a : ℕ → ℕ) (B n : ℕ) : ℕ → ℕ :=
  rampN (padSeq a n (detH B)) (detR B n)

/-- The fully processed second operand: extend, pad, then ramp. -/
def detB (b : ℕ → ℕ) (B n t : ℕ) : ℕ → ℕ :=
  rampN (padSeq (detExt b n t) n (detH B)) (detR B n)

/-- **The composed reduction, fully executable.** For ANY sequences
`a, b` bounded by `B` on `[0, n]` and any diagonal `d ≤ 2n`: the
processed operands are strictly increasing (so their encodings are
well-formed inputs to the verified pipeline), the processed upper-half
MinConv at `2n + d` is exactly the genuine full-MinConv value at `d`
plus the known ramp shift, and querying the executable
`sparsify 1 ∘ conv` merge at `t` decides that value's position via
block logarithms. Every step is machine-checked; no prose remains in
the reduction. -/
theorem det_reduction_complete
    (a b : ℕ → ℕ) (n d B t w : ℕ)
    (hn : 1 ≤ n) (hd : d ≤ 2 * n)
    (hB : ∀ k, k ≤ n → a k ≤ B) (hB' : ∀ k, k ≤ n → b k ≤ B)
    (ht : 2 * B + n ≤ t)
    (hw : 2 * (2 * n + 1) ^ 2 < 2 ^ w)
    (htlo : minConvN (detA a B n) (detB b B n t) (2 * n) (2 * n) ≤ t) :
    -- (i) the processed MinConv value is the genuine one, attained:
    (∃ k, k ≤ d ∧ k ≤ n ∧ d - k ≤ n ∧
      minConvN (detA a B n) (detB b B n t) (2 * n) (2 * n + d) =
        a k + b (d - k) + detR B n * (2 * n + d)) ∧
    -- (ii) and minimal over all genuine pairs:
    (∀ k, k ≤ d → k ≤ n → d - k ≤ n →
      minConvN (detA a B n) (detB b B n t) (2 * n) (2 * n + d) ≤
        a k + b (d - k) + detR B n * (2 * n + d)) ∧
    -- (iii) the executable merge output decides it:
    (minConvN (detA a B n) (detB b B n t) (2 * n) (2 * n + d) ≤ t ↔
      2 * n + d ≤
        Nat.log 2 (queryLe (sparsify 1
          (conv (encodeSF (detA a B n) (2 * n) w)
                (encodeSF (detB b B n t) (2 * n) w))) t) / w) := by
  set H := detH B with hHdef
  set R := detR B n with hRdef
  have hHB : 2 * B < H := by
    rw [hHdef]
    unfold detH
    omega
  have hRbig : H + n < R := by
    rw [hRdef]
    unfold detR
    omega
  -- pad bounds: within [0, 2n] both padded sequences are ≤ H + n
  have hpadA : ∀ k, k ≤ 2 * n → padSeq a n H k ≤ H + n := by
    intro k hk
    unfold padSeq
    by_cases h : k < n
    · rw [if_pos h]
      omega
    · rw [if_neg h]
      have := hB (k - n) (by omega)
      unfold detH at hHdef
      omega
  have hpadB : ∀ k, k ≤ 2 * n → padSeq (detExt b n t) n H k ≤ H + n := by
    intro k hk
    unfold padSeq
    by_cases h : k < n
    · rw [if_pos h]
      omega
    · rw [if_neg h]
      unfold detExt
      rw [if_pos (by omega)]
      have := hB' (k - n) (by omega)
      unfold detH at hHdef
      omega
  -- strict monotonicity of the processed operands on [0, 2n]
  have hstepA : ∀ k, k + 1 ≤ 2 * n → detA a B n k < detA a B n (k + 1) := by
    intro k hk
    unfold detA rampN
    rw [← hHdef, ← hRdef]
    have h1 := hpadA k (by omega)
    have h2 : R * k + R ≤ R * (k + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
    omega
  have hstepB : ∀ k, k + 1 ≤ 2 * n →
      detB b B n t k < detB b B n t (k + 1) := by
    intro k hk
    unfold detB rampN
    rw [← hHdef, ← hRdef]
    have h1 := hpadB k (by omega)
    have h2 : R * k + R ≤ R * (k + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
    omega
  have hincA : ∀ i j, i < j → j ≤ 2 * n → detA a B n i < detA a B n j := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ jj ih =>
      rcases Nat.lt_or_ge i jj with hlt | hge
      · exact lt_trans (ih hlt (by omega)) (hstepA jj hj)
      · have : i = jj := by omega
        rw [this]
        exact hstepA jj hj
  have hincB : ∀ i j, i < j → j ≤ 2 * n →
      detB b B n t i < detB b B n t j := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ jj ih =>
      rcases Nat.lt_or_ge i jj with hlt | hge
      · exact lt_trans (ih hlt (by omega)) (hstepB jj hj)
      · have : i = jj := by omega
        rw [this]
        exact hstepB jj hj
  -- the second operand is huge beyond the instance
  have hbig : ∀ l, 2 * n < l → t < detB b B n t l := by
    intro l hl
    unfold detB rampN padSeq
    rw [← hHdef, ← hRdef, if_neg (by omega)]
    unfold detExt
    rw [if_neg (by omega)]
    omega
  -- global monotonicity of the second operand (for the frontier bridge)
  have hmonoB : ∀ i j, i ≤ j → detB b B n t i ≤ detB b B n t j := by
    intro i j hij
    rcases Nat.eq_or_lt_of_le hij with heq | hlt
    · rw [heq]
    · rcases Nat.lt_or_ge (2 * n) j with hj2n | hj2n
      · -- j beyond the instance: the huge form
        have hjform : detB b B n t j = t + 1 + R * j := by
          unfold detB rampN padSeq
          rw [← hHdef, ← hRdef, if_neg (by omega)]
          unfold detExt
          rw [if_neg (by omega)]
        rcases Nat.lt_or_ge (2 * n) i with hi2n | hi2n
        · -- both beyond: compare huge forms
          have hiform : detB b B n t i = t + 1 + R * i := by
            unfold detB rampN padSeq
            rw [← hHdef, ← hRdef, if_neg (by omega)]
            unfold detExt
            rw [if_neg (by omega)]
          rw [hiform, hjform]
          have h4 : R * i ≤ R * j := Nat.mul_le_mul_left _ hij
          omega
        · -- i inside, j beyond
          calc detB b B n t i
              ≤ H + n + R * (2 * n) := by
                unfold detB rampN
                rw [← hHdef, ← hRdef]
                have := hpadB i hi2n
                have h2 : R * i ≤ R * (2 * n) := Nat.mul_le_mul_left _ hi2n
                omega
            _ ≤ t + 1 + R * j := by
                have h4 : R * (2 * n) ≤ R * j := Nat.mul_le_mul_left _ (by omega)
                unfold detR at hRdef
                unfold detH at hHdef
                omega
            _ = detB b B n t j := hjform.symm
      · exact le_of_lt (hincB i j hlt hj2n)
  -- (i) attainment via the pad lemma, transported through the ramp
  have hH1 : ∀ k l, k ≤ n → l ≤ n → a k + detExt b n t l < H := by
    intro k l hk hl
    unfold detExt
    rw [if_pos hl]
    have := hB k hk
    have := hB' l hl
    omega
  have hHb : ∀ l, n < l → H ≤ detExt b n t l := by
    intro l hl
    unfold detExt
    rw [if_neg (by omega), hHdef]
    unfold detH
    omega
  obtain ⟨k₀, hk₀d, hk₀n, hk₀dk, hk₀dn, hk₀eq⟩ :=
    minConv_pad_attained a (detExt b n t) n d H hd hH1 hHb
  have hramp := rampN_minConv (padSeq a n H) (padSeq (detExt b n t) n H)
    R (2 * n) (2 * n + d) (by omega)
  have hAB : minConvN (detA a B n) (detB b B n t) (2 * n) (2 * n + d) =
      minConvN (padSeq a n H) (padSeq (detExt b n t) n H) (2 * n) (2 * n + d) +
        R * (2 * n + d) := hramp
  refine ⟨⟨k₀, hk₀d, hk₀n, hk₀dk, ?_⟩, ?_, ?_⟩
  · rw [hAB, hk₀eq]
    have : detExt b n t (d - k₀) = b (d - k₀) := by
      unfold detExt
      rw [if_pos hk₀dk]
    rw [this]
  · intro k hkd hkn hdkn
    rw [hAB]
    have h1 := minConv_pad_le a (detExt b n t) n d H k hkd hkn hdkn
    have h2 : detExt b n t (d - k) = b (d - k) := by
      unfold detExt
      rw [if_pos hdkn]
    rw [h2] at h1
    omega
  · -- (iii): sparsified read-off + frontier bridge
    have hreadoff := readoff_sparsified (detA a B n) (detB b B n t)
      (2 * n) w t hw hincA hincB htlo hbig
    rw [hreadoff]
    exact frontierN_readoff (detA a B n) (detB b B n t) (2 * n)
      (2 * n + d) t (by omega) (by omega) (by omega)
      (fun m₁ m₂ h1 h2 h3 =>
        minConvN_mono (detA a B n) (detB b B n t) (2 * n) hmonoB m₁ m₂ h2)
