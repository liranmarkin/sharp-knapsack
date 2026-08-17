/-
# Sparse representation of functions (paper Definition 7)

The algorithms represent a function `f : ℕ → ℕ` as the sorted list of pairs
`(x, f x)` with `f x > 0` (paper Definition 7). This file defines that
representation (`SparseFun`), its denotation `eval` back to honest functions,
well-formedness (`WF`: strictly sorted keys, positive values), and the
executable operations *summation*, *shifting*, *convolution*, and *query*
of paper Section 2, each with a specification lemma tying it to the abstract
operation of `Approx.lean`.

(The remaining operation, *sparsification*, has its own file: `Sparsify.lean`.)
-/

import SharpKnapsack.Count

open Finset

/-- A sparse function: a list of (position, value) pairs. -/
abbrev SparseFun := List (ℕ × ℕ)

/-- The indicator function placing value `v` at position `a`. -/
def single (a v : ℕ) : ℕ → ℕ := fun x => if a = x then v else 0

namespace SparseFun

/-- The function a sparse list denotes: sum of the values at position `x`.
(If a position occurs several times, the values add up - normalization removes
such duplicates, but the semantics never depends on well-formedness.) -/
def eval (L : SparseFun) : ℕ → ℕ := fun x => (L.map fun p => if p.1 = x then p.2 else 0).sum

/-- Well-formed representation: keys strictly increasing, values positive. -/
def WF (L : SparseFun) : Prop :=
  L.Pairwise (fun p q => p.1 < q.1) ∧ ∀ p ∈ L, 0 < p.2

theorem eval_nil : eval ([] : SparseFun) = fun _ => 0 := rfl

theorem eval_cons (a v : ℕ) (L : SparseFun) (x : ℕ) :
    eval ((a, v) :: L) x = single a v x + eval L x := by
  simp [eval, single]

theorem eval_append (L M : SparseFun) (x : ℕ) :
    eval (L ++ M) x = eval L x + eval M x := by
  simp [eval]

theorem eval_perm {L M : SparseFun} (h : L.Perm M) : eval L = eval M := by
  funext x
  exact List.Perm.sum_eq (h.map _)

theorem prefixLe_eval_append (L M : SparseFun) (x : ℕ) :
    prefixLe (eval (L ++ M)) x = prefixLe (eval L) x + prefixLe (eval M) x := by
  have h : eval (L ++ M) = fun t => eval L t + eval M t :=
    funext fun t => eval_append L M t
  rw [h, prefixLe_add]

/-! ## Query (paper Section 2, "Query") -/

/-- `queryLe L C` = the sum of all values at positions `≤ C` - the executable
form of `(eval L)^≤(C)`. -/
def queryLe (L : SparseFun) (C : ℕ) : ℕ :=
  ((L.filter fun p => p.1 ≤ C).map (·.2)).sum

theorem prefixLe_single (a v C : ℕ) :
    prefixLe (single a v) C = if a ≤ C then v else 0 := by
  induction C with
  | zero =>
    rcases Nat.eq_zero_or_pos a with h | h
    · subst h; simp [prefixLe_zero, single]
    · have : ¬ a = 0 := by omega
      have h' : ¬ a ≤ 0 := by omega
      simp [prefixLe_zero, single, this, h']
  | succ C ih =>
    rw [prefixLe_succ, ih]
    by_cases h : a ≤ C
    · have h' : a ≤ C + 1 := by omega
      have : ¬ a = C + 1 := by omega
      simp [single, h, h', this]
    · by_cases h' : a ≤ C + 1
      · have : a = C + 1 := by omega
        simp [single, h, h', this]
      · have : ¬ a = C + 1 := by omega
        simp [single, h, h', this]

/-- Specification of `queryLe`: it computes the prefix sum of the denotation. -/
theorem queryLe_spec (L : SparseFun) (C : ℕ) :
    queryLe L C = prefixLe (eval L) C := by
  induction L with
  | nil => simp [queryLe, eval_nil, prefixLe]
  | cons p L ih =>
    have hev : eval (p :: L) = fun x => single p.1 p.2 x + eval L x := by
      funext x; exact eval_cons p.1 p.2 L x
    rw [hev, prefixLe_add, ← ih, prefixLe_single]
    unfold queryLe
    by_cases h : p.1 ≤ C <;> simp [List.filter_cons, h]

/-! ## Shifting (paper Section 2, "Shifting") -/

/-- Shift a sparse function by `w`: move every point right by `w`. -/
def shift (w : ℕ) (L : SparseFun) : SparseFun := L.map fun p => (p.1 + w, p.2)

theorem shift_spec (w : ℕ) (L : SparseFun) :
    eval (shift w L) = shiftFun w (eval L) := by
  funext x
  induction L with
  | nil => simp [shift, eval_nil, shiftFun]
  | cons p L ih =>
    obtain ⟨a, v⟩ := p
    have h1 : eval (shift w ((a, v) :: L)) x = single (a + w) v x + eval (shift w L) x := by
      simp [shift, eval, single]
    have h2 : shiftFun w (eval ((a, v) :: L)) x
        = shiftFun w (single a v) x + shiftFun w (eval L) x := by
      by_cases h : w ≤ x <;> simp [shiftFun, h, eval_cons]
    rw [h1, h2, ih]
    congr 1
    unfold single shiftFun
    by_cases h : w ≤ x
    · have : (a + w = x) ↔ (a = x - w) := by omega
      simp [h, this]
    · have : ¬ (a + w = x) := by omega
      simp [h, this]

theorem shift_wf {L : SparseFun} (h : WF L) (w : ℕ) : WF (shift w L) := by
  obtain ⟨hs, hp⟩ := h
  constructor
  · exact (List.pairwise_map.mpr (hs.imp (by intro a b hab; omega)))
  · intro p hp'
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp'
    exact hp q hq

/-! ## Normalization: sort by position and merge duplicates

`add` and `conv` first produce an unsorted list of points, then `normalize`
it. Normalization never changes the denotation and always produces a
well-formed representation.
-/

/-- Merge adjacent pairs that share a position. -/
def mergeDups : SparseFun → SparseFun
  | [] => []
  | [p] => [p]
  | (x, v) :: (y, w) :: L =>
    if x = y then mergeDups ((x, v + w) :: L)
    else (x, v) :: mergeDups ((y, w) :: L)
termination_by l => l.length

theorem eval_mergeDups (L : SparseFun) : eval (mergeDups L) = eval L := by
  induction L using mergeDups.induct with
  | case1 => simp [mergeDups]
  | case2 p => simp [mergeDups]
  | case3 v y w L ih =>
    rw [mergeDups, if_pos rfl, ih]
    funext t
    rw [eval_cons, eval_cons, eval_cons]
    unfold single
    split <;> omega
  | case4 x v y w L hne ih =>
    rw [mergeDups, if_neg hne]
    funext t
    rw [eval_cons, eval_cons]
    rw [ih]

/-- Every position in the output of `mergeDups` was a position of the input. -/
theorem mergeDups_keys (L : SparseFun) :
    ∀ p ∈ mergeDups L, ∃ q ∈ L, p.1 = q.1 := by
  induction L using mergeDups.induct with
  | case1 => simp [mergeDups]
  | case2 p => simp [mergeDups]
  | case3 v y w L ih =>
    rw [mergeDups, if_pos rfl]
    intro p hp
    obtain ⟨q, hq, hpq⟩ := ih p hp
    rcases List.mem_cons.mp hq with rfl | hq'
    · exact ⟨(y, v), by simp, hpq⟩
    · exact ⟨q, by simp [hq'], hpq⟩
  | case4 x v y w L hne ih =>
    rw [mergeDups, if_neg hne]
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp'
    · exact ⟨(x, v), by simp, rfl⟩
    · obtain ⟨q, hq, hpq⟩ := ih p hp'
      exact ⟨q, by simp [List.mem_cons.mp hq], hpq⟩

theorem mergeDups_sorted {L : SparseFun}
    (h : L.Pairwise (fun p q => p.1 ≤ q.1)) :
    (mergeDups L).Pairwise (fun p q => p.1 < q.1) := by
  induction L using mergeDups.induct with
  | case1 => simp [mergeDups]
  | case2 p => simp [mergeDups]
  | case3 v y w L ih =>
    rw [mergeDups, if_pos rfl]
    refine ih ?_
    rw [List.pairwise_cons] at h ⊢
    obtain ⟨h1, h2⟩ := h
    rw [List.pairwise_cons] at h2
    exact ⟨fun p hp => h2.1 p hp, h2.2⟩
  | case4 x v y w L hne ih =>
    rw [mergeDups, if_neg hne]
    rw [List.pairwise_cons] at h
    obtain ⟨h1, h2⟩ := h
    have hxy : x < y := by
      have h' := h1 (y, w) (by simp)
      simp at h'
      omega
    refine List.pairwise_cons.mpr ⟨?_, ih h2⟩
    intro p hp
    obtain ⟨q, hq, hpq⟩ := mergeDups_keys _ p hp
    rcases List.mem_cons.mp hq with rfl | hq'
    · simpa [hpq] using hxy
    · have h2' := h2
      rw [List.pairwise_cons] at h2'
      have h'' := h2'.1 q hq'
      simp at h''
      simp [hpq]
      omega

theorem mergeDups_pos {L : SparseFun} (h : ∀ p ∈ L, 0 < p.2) :
    ∀ p ∈ mergeDups L, 0 < p.2 := by
  induction L using mergeDups.induct with
  | case1 => simp [mergeDups]
  | case2 p =>
    intro q hq
    rw [mergeDups] at hq
    exact h q hq
  | case3 v y w L ih =>
    rw [mergeDups, if_pos rfl]
    refine ih ?_
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp'
    · have h1 := h (y, v) (by simp)
      have h2 := h (y, w) (by simp)
      simp at h1 h2 ⊢
      omega
    · exact h p (by simp [hp'])
  | case4 x v y w L hne ih =>
    rw [mergeDups, if_neg hne]
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp'
    · exact h (x, v) (by simp)
    · exact ih (fun q hq => h q (by simp [List.mem_cons.mp hq])) p hp'

/-- Sort by position, then merge duplicate positions. The result denotes the
same function and is always well-formed. -/
def normalize (L : SparseFun) : SparseFun :=
  mergeDups (L.mergeSort (fun p q => p.1 ≤ q.1))

theorem normalize_eval (L : SparseFun) : eval (normalize L) = eval L := by
  unfold normalize
  rw [eval_mergeDups]
  exact eval_perm (List.mergeSort_perm L _)

theorem normalize_sorted (L : SparseFun) :
    (normalize L).Pairwise (fun p q => p.1 < q.1) := by
  unfold normalize
  exact mergeDups_sorted (List.pairwise_mergeSort' (fun p q => p.1 ≤ q.1) L)

theorem normalize_pos {L : SparseFun} (h : ∀ p ∈ L, 0 < p.2) :
    ∀ p ∈ normalize L, 0 < p.2 := by
  unfold normalize
  refine mergeDups_pos ?_
  intro p hp
  exact h p ((List.mergeSort_perm L _).mem_iff.mp hp)

theorem normalize_wf {L : SparseFun} (h : ∀ p ∈ L, 0 < p.2) : WF (normalize L) :=
  ⟨normalize_sorted L, normalize_pos h⟩

/-! ## Summation (paper Section 2, "Summation") -/

/-- Pointwise sum of two sparse functions. -/
def add (L M : SparseFun) : SparseFun := normalize (L ++ M)

theorem add_spec (L M : SparseFun) :
    eval (add L M) = fun x => eval L x + eval M x := by
  funext x
  rw [add, normalize_eval, eval_append]

theorem add_wf {L M : SparseFun} (hL : WF L) (hM : WF M) : WF (add L M) := by
  refine normalize_wf ?_
  intro p hp
  rcases List.mem_append.mp hp with h | h
  · exact hL.2 p h
  · exact hM.2 p h

/-! ## Convolution (paper Section 2, "Convolution") -/

/-- Convolution: all pairwise combinations `(x₁ + x₂, v₁ · v₂)`, normalized. -/
def conv (L M : SparseFun) : SparseFun :=
  normalize (L.flatMap fun p => M.map fun q => (p.1 + q.1, p.2 * q.2))

theorem convFun_single_left (a v : ℕ) (g : ℕ → ℕ) :
    convFun (single a v) g = fun x => v * shiftFun a g x := by
  funext x
  unfold convFun shiftFun
  by_cases h : a ≤ x
  · rw [sum_eq_single a]
    · simp [single, h]
    · intro y _ hy
      simp [single, Ne.symm hy]
    · intro ha
      exfalso
      exact ha (mem_range.mpr (by omega))
  · rw [sum_eq_zero, if_neg h, Nat.mul_zero]
    intro y hy
    have : ¬ a = y := by have := mem_range.mp hy; omega
    simp [single, this]

theorem eval_map_pairs (a v : ℕ) (M : SparseFun) (x : ℕ) :
    eval (M.map fun q => (a + q.1, v * q.2)) x = v * shiftFun a (eval M) x := by
  induction M with
  | nil => simp [eval, shiftFun]
  | cons q M ih =>
    obtain ⟨b, u⟩ := q
    have h1 : eval (((a + b, v * u)) :: M.map fun q => (a + q.1, v * q.2)) x
        = single (a + b) (v * u) x + eval (M.map fun q => (a + q.1, v * q.2)) x :=
      eval_cons _ _ _ x
    have h2 : shiftFun a (eval ((b, u) :: M)) x
        = shiftFun a (single b u) x + shiftFun a (eval M) x := by
      by_cases h : a ≤ x <;> simp [shiftFun, h, eval_cons]
    simp only [List.map_cons]
    rw [h1, h2, Nat.mul_add, ih]
    congr 1
    unfold single shiftFun
    by_cases h : a ≤ x
    · have : (a + b = x) ↔ (b = x - a) := by omega
      simp [h, this]
    · have : ¬ (a + b = x) := by omega
      simp [h, this]

/-- The raw (un-normalized) product list denotes the convolution. -/
theorem eval_conv_raw (L M : SparseFun) :
    eval (L.flatMap fun p => M.map fun q => (p.1 + q.1, p.2 * q.2))
      = convFun (eval L) (eval M) := by
  induction L with
  | nil =>
    funext x
    simp [eval, convFun]
  | cons p L ih =>
    obtain ⟨a, v⟩ := p
    funext x
    rw [List.flatMap_cons, eval_append, ih]
    have hev : eval ((a, v) :: L) = fun t => single a v t + eval L t :=
      funext fun t => eval_cons a v L t
    rw [hev, convFun_add_left, convFun_single_left]
    simp only []
    rw [eval_map_pairs]

theorem conv_spec (L M : SparseFun) :
    eval (conv L M) = convFun (eval L) (eval M) := by
  unfold conv
  rw [normalize_eval, eval_conv_raw]

theorem conv_wf {L M : SparseFun} (hL : WF L) (hM : WF M) : WF (conv L M) := by
  refine normalize_wf ?_
  intro p hp
  obtain ⟨q, hq, hp'⟩ := List.mem_flatMap.mp hp
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hp'
  exact Nat.mul_pos (hL.2 q hq) (hM.2 r hr)

end SparseFun
