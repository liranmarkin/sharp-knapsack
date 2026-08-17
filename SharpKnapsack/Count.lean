/-
# Counting knapsack solutions (paper Sections 3-4)

`count S x` is the paper's `k_S(x)`: the number of sub(multi)sets of the
weight list `S` whose total weight is exactly `x`. It is *defined*
combinatorially, by literally filtering all sublists - this is the trusted
specification the final theorem refers to (and it is executable, serving as
the brute-force reference in tests).

The two structural lemmas of the paper are proved about it:

* **Lemma 9**: `k_{S ∪ {w}} = k_S + k_S|_w` (insert one item);
* **Lemma 10**: `k_{S ∪ T} = k_S * k_T` (convolution of two halves).
-/

import SharpKnapsack.Approx

open Finset

/-- `count S x` = number of sublists of `S` with sum exactly `x`
(the paper's `k_S(x)`). Each element of `S` may be used at most once;
duplicate weights in `S` are distinct items. -/
def count (S : List ℕ) (x : ℕ) : ℕ :=
  (S.sublists'.filter fun t => decide (t.sum = x)).length

/-- `countLe S C` = number of sublists of `S` with sum at most `C` - the
answer to the #Knapsack instance `(S, C)` (the paper's `k_S^≤(C)`). -/
def countLe (S : List ℕ) (C : ℕ) : ℕ := prefixLe (count S) C

theorem count_nil (x : ℕ) : count [] x = if x = 0 then 1 else 0 := by
  rcases x with _ | x <;> simp [count]

/-- **Lemma 9**: inserting an item `w` into the set `S` transforms the count
into `k_S + k_S|_w`: a subset either omits `w` (counted by `k_S`) or contains
it (counted by `k_S` shifted by `w`). -/
theorem count_cons (w : ℕ) (S : List ℕ) (x : ℕ) :
    count (w :: S) x = count S x + shiftFun w (count S) x := by
  unfold count
  rw [List.sublists'_cons, List.filter_append, List.length_append]
  congr 1
  rw [List.filter_map, List.length_map]
  simp only [Function.comp_def]
  by_cases h : w ≤ x
  · have hpred : ∀ t ∈ S.sublists',
        (decide ((w :: t).sum = x)) = (decide (t.sum = x - w)) := fun t _ => by
      rw [decide_eq_decide, List.sum_cons]
      omega
    rw [List.filter_congr hpred]
    simp [shiftFun, h]
  · have hpred : ∀ t ∈ S.sublists',
        (decide ((w :: t).sum = x)) = false := fun t _ => by
      rw [decide_eq_false_iff_not, List.sum_cons]
      omega
    have : (S.sublists'.filter fun t => decide ((w :: t).sum = x)) = [] := by
      rw [List.filter_congr hpred (q := fun _ => false)]
      exact List.filter_false _
    rw [this]
    simp [shiftFun, h]

/-! ## Convolution algebra needed for Lemma 10 -/

/-- The counting function of the empty set is the unit of convolution. -/
theorem convFun_unit_left (g : ℕ → ℕ) :
    convFun (fun x => if x = 0 then 1 else 0) g = g := by
  funext x
  unfold convFun
  rw [sum_eq_single 0]
  · simp
  · intro y _ hy
    simp [hy]
  · intro h
    simp at h

/-- Convolution distributes over pointwise sum on the left. -/
theorem convFun_add_left (f₁ f₂ g : ℕ → ℕ) :
    convFun (fun x => f₁ x + f₂ x) g = fun x => convFun f₁ g x + convFun f₂ g x := by
  funext x
  unfold convFun
  rw [← sum_add_distrib]
  exact sum_congr rfl fun y _ => by ring

/-- Convolution commutes with shifting on the left: `(f|_w) * g = (f * g)|_w`. -/
theorem convFun_shift_left (w : ℕ) (f g : ℕ → ℕ) :
    convFun (shiftFun w f) g = shiftFun w (convFun f g) := by
  funext x
  by_cases h : w ≤ x
  · unfold convFun shiftFun
    simp only [h, if_true]
    rw [show (∑ y ∈ range (x + 1), (if w ≤ y then f (y - w) else 0) * g (x - y))
        = ∑ y ∈ range (x + 1), (if w ≤ y then f (y - w) * g (x - y) else 0) from
      sum_congr rfl fun y _ => by split <;> simp]
    rw [← sum_filter]
    have hIco : (range (x + 1)).filter (fun y => w ≤ y) = Ico w (x + 1) := by
      ext z; simp [mem_filter, mem_range, mem_Ico]; omega
    rw [hIco, sum_Ico_eq_sum_range]
    have hn : x + 1 - w = (x - w) + 1 := by omega
    rw [hn]
    exact sum_congr rfl fun z hz => by
      have hz' : z ≤ x - w := by simpa [Nat.lt_succ_iff] using mem_range.mp hz
      have e1 : w + z - w = z := by omega
      have e2 : x - (w + z) = (x - w) - z := by omega
      rw [e1, e2]
  · unfold convFun shiftFun
    simp only [h, if_false]
    refine sum_eq_zero fun y hy => ?_
    have : ¬ w ≤ y := by
      have := mem_range.mp hy; omega
    simp [this]

/-- **Lemma 10**: splitting the set into two halves turns the count into a
convolution: `k_{A ∪ B} = k_A * k_B`. Proved by induction on `A`, moving one
item at a time across the convolution using Lemma 9 and the convolution
algebra above. -/
theorem count_append (A B : List ℕ) :
    count (A ++ B) = convFun (count A) (count B) := by
  induction A with
  | nil =>
    have h : count ([] : List ℕ) = fun x => if x = 0 then 1 else 0 :=
      funext count_nil
    rw [List.nil_append, h, convFun_unit_left]
  | cons w A ih =>
    have h9l : count (w :: (A ++ B)) = fun x =>
        count (A ++ B) x + shiftFun w (count (A ++ B)) x := funext (count_cons w (A ++ B))
    have h9r : count (w :: A) = fun x => count A x + shiftFun w (count A) x :=
      funext (count_cons w A)
    calc count ((w :: A) ++ B) = count (w :: (A ++ B)) := by simp
      _ = fun x => count (A ++ B) x + shiftFun w (count (A ++ B)) x := h9l
      _ = fun x => convFun (count A) (count B) x
            + shiftFun w (convFun (count A) (count B)) x := by rw [ih]
      _ = fun x => convFun (count A) (count B) x
            + convFun (shiftFun w (count A)) (count B) x := by
          rw [convFun_shift_left]
      _ = convFun (fun x => count A x + shiftFun w (count A) x) (count B) := by
          rw [convFun_add_left]
      _ = convFun (count (w :: A)) (count B) := by rw [h9r]
