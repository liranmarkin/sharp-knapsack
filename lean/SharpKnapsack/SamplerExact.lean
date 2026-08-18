/-
# Stage A of the witness-sampler verification: the exact sampler is uniform

Outcomes are Boolean masks over the item list (`m : List Bool`, one bit per
item), so duplicate weights are distinct items and every draw has a unique
decomposition. `maskSum m S` is the selected weight.

`splitMass S s m` is the probability that the divide-and-conquer sampler,
conditioned on total (exact) weight `s`, outputs mask `m`: at a leaf it is
the uniform table draw; at an internal node it draws the left-half weight
`y` with probability `count L y · count R (s−y) / count S s` (the split
distribution of `docs/witness-sampler.md`, step 3) and recurses on both
halves with exact weights. `samplerMass S t m` adds the root capacity draw
`s ∝ count S s` over `s ≤ t` (step 1 - the only place `t` appears).

Main theorems (`splitMass_spec`, `samplerMass_spec`): these mass functions
are EXACTLY the uniform distribution over masks with `maskSum = s`
(resp. `≤ t`). This machine-checks the new algorithmic content of the
sampler - the exact-total factorization and the split recursion - in the
exact-count setting; approximate arrays are Stage B
(`docs/verification-roadmap.md`).
-/
import SharpKnapsack.Count

open Finset

/-- Weight selected by mask `m` from item list `S` (junk-free only when
`m.length = S.length`, which all theorems assume). -/
def maskSum : List Bool → List ℕ → ℕ
  | b :: m, w :: S => (if b then w else 0) + maskSum m S
  | _, _ => 0

theorem maskSum_nil_left (S : List ℕ) : maskSum [] S = 0 := by
  cases S <;> rfl

theorem maskSum_append (m₁ m₂ : List Bool) (S₁ S₂ : List ℕ)
    (h : m₁.length = S₁.length) :
    maskSum (m₁ ++ m₂) (S₁ ++ S₂) = maskSum m₁ S₁ + maskSum m₂ S₂ := by
  induction m₁ generalizing S₁ with
  | nil =>
    cases S₁ with
    | nil => simp [maskSum_nil_left]
    | cons w S => simp at h
  | cons b m ih =>
    cases S₁ with
    | nil => simp at h
    | cons w S =>
      have h' : m.length = S.length := by simpa using h
      simp only [List.cons_append, maskSum, ih S h']
      omega

/-- Splitting a mask and the items at the same position splits the sum. -/
theorem maskSum_take_drop (k : ℕ) (m : List Bool) (S : List ℕ)
    (h : m.length = S.length) :
    maskSum m S = maskSum (m.take k) (S.take k) + maskSum (m.drop k) (S.drop k) := by
  have hlen : (m.take k).length = (S.take k).length := by
    simp [List.length_take, h]
  calc maskSum m S
      = maskSum (m.take k ++ m.drop k) (S.take k ++ S.drop k) := by
        rw [List.take_append_drop, List.take_append_drop]
    _ = maskSum (m.take k) (S.take k) + maskSum (m.drop k) (S.drop k) :=
        maskSum_append _ _ _ _ hlen

/-- Every mask witnesses a positive count at its own weight. -/
theorem count_pos_of_mask (S : List ℕ) (m : List Bool)
    (h : m.length = S.length) : 0 < count S (maskSum m S) := by
  induction S generalizing m with
  | nil =>
    cases m with
    | nil => simp [maskSum, count_nil]
    | cons b m' => simp at h
  | cons w S ih =>
    cases m with
    | nil => simp at h
    | cons b m' =>
      have h' : m'.length = S.length := by simpa using h
      rw [count_cons]
      cases b with
      | false =>
        have hm : maskSum (false :: m') (w :: S) = maskSum m' S := by
          simp [maskSum]
        rw [hm]
        exact lt_of_lt_of_le (ih m' h') (Nat.le_add_right _ _)
      | true =>
        have hm : maskSum (true :: m') (w :: S) = w + maskSum m' S := by
          simp [maskSum]
        rw [hm]
        have hs : shiftFun w (count S) (w + maskSum m' S) = count S (maskSum m' S) := by
          simp [shiftFun]
        have := ih m' h'
        omega

/-- Conditional mass function of the exact-sum split sampler: probability of
outputting mask `m` given the subtree's exact total is `s`. Leaves
(`length ≤ 1`) are uniform table draws; internal nodes draw the split `y`
from `count L y · count R (s−y) / count S s` and recurse. -/
def splitMass (S : List ℕ) (s : ℕ) (m : List Bool) : ℚ :=
  if S.length ≤ 1 then
    if m.length = S.length ∧ maskSum m S = s then ((count S s : ℚ))⁻¹ else 0
  else
    ∑ y ∈ range (s + 1),
      ((count (S.take (S.length / 2)) y * count (S.drop (S.length / 2)) (s - y) : ℕ) : ℚ)
          / ((count S s : ℕ) : ℚ)
        * splitMass (S.take (S.length / 2)) y (m.take (S.length / 2))
        * splitMass (S.drop (S.length / 2)) (s - y) (m.drop (S.length / 2))
termination_by S.length
decreasing_by
  · simp only [List.length_take]
    omega
  · simp only [List.length_drop]
    omega

/-- **The exact split sampler is uniform**: conditioned on total `s`, every
mask of weight `s` has probability exactly `1 / count S s`, every other
mask probability `0`. -/
theorem splitMass_spec (S : List ℕ) (s : ℕ) (m : List Bool) :
    splitMass S s m =
      if m.length = S.length ∧ maskSum m S = s then ((count S s : ℚ))⁻¹ else 0 := by
  induction hn : S.length using Nat.strong_induction_on generalizing S s m with
  | _ n IH =>
  subst hn
  rw [splitMass]
  by_cases hlen : S.length ≤ 1
  · rw [if_pos hlen]
  rw [if_neg hlen]
  have hlen1 : 1 < S.length := by omega
  set k := S.length / 2 with hk
  set L := S.take k with hL
  set R := S.drop k with hR
  have hLlen : L.length = k := by
    simp [hL, List.length_take]
    omega
  have hRlen : R.length = S.length - k := by
    simp [hR, List.length_drop]
  have hkpos : 1 ≤ k := by omega
  have hklt : k < S.length := by omega
  have IHL : ∀ y mL, splitMass L y mL =
      if mL.length = L.length ∧ maskSum mL L = y then ((count L y : ℚ))⁻¹ else 0 :=
    fun y mL => IH L.length (by omega) L y mL rfl
  have IHR : ∀ y mR, splitMass R y mR =
      if mR.length = R.length ∧ maskSum mR R = y then ((count R y : ℚ))⁻¹ else 0 :=
    fun y mR => IH R.length (by omega) R y mR rfl
  by_cases hm : m.length = S.length ∧ maskSum m S = s
  · -- the solution case: only y₀ = weight of the left half survives
    obtain ⟨hmlen, hmsum⟩ := hm
    rw [if_pos ⟨hmlen, hmsum⟩]
    have hmL : (m.take k).length = L.length := by
      simp [hLlen, List.length_take]
      omega
    have hmR : (m.drop k).length = R.length := by
      simp [hRlen, List.length_drop]
      omega
    set y₀ := maskSum (m.take k) L with hy₀
    have hsplit : maskSum m S = y₀ + maskSum (m.drop k) R := by
      have h := maskSum_take_drop k m S hmlen
      rw [← hL, ← hR] at h
      rw [← hy₀] at h
      exact h
    have hy₀le : y₀ ≤ s := by omega
    have hRsum : maskSum (m.drop k) R = s - y₀ := by omega
    have hcL : 0 < count L y₀ := hy₀ ▸ count_pos_of_mask L (m.take k) hmL
    have hcR : 0 < count R (s - y₀) := hRsum ▸ count_pos_of_mask R (m.drop k) hmR
    have hcS : 0 < count S s := hmsum ▸ count_pos_of_mask S m hmlen
    rw [Finset.sum_eq_single_of_mem y₀ (by simp [Finset.mem_range]; omega)]
    · rw [IHL, IHR, if_pos ⟨hmL, rfl⟩, if_pos ⟨hmR, hRsum⟩]
      have hcLQ : ((count L y₀ : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hcL.ne'
      have hcRQ : ((count R (s - y₀) : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hcR.ne'
      have hcSQ : ((count S s : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hcS.ne'
      push_cast
      field_simp
    · intro y _ hy
      rw [IHL]
      have : ¬((m.take k).length = L.length ∧ maskSum (m.take k) L = y) := by
        rintro ⟨-, h2⟩
        exact hy (by rw [← h2])
      rw [if_neg this]
      ring
  · -- the zero case: every summand vanishes
    rw [if_neg hm]
    apply Finset.sum_eq_zero
    intro y hy
    rw [Finset.mem_range] at hy
    by_cases hmlen : m.length = S.length
    · -- lengths match, so the weight must be wrong somewhere
      have hmL : (m.take k).length = L.length := by
        simp [hLlen, List.length_take]
        omega
      have hmR : (m.drop k).length = R.length := by
        simp [hRlen, List.length_drop]
        omega
      have hmsum : maskSum m S ≠ s := fun h => hm ⟨hmlen, h⟩
      by_cases hyL : maskSum (m.take k) L = y
      · -- left weight matches y, so the right weight cannot match s − y
        have hsplit : maskSum m S = y + maskSum (m.drop k) R := by
          have h := maskSum_take_drop k m S hmlen
          rw [← hL, ← hR, hyL] at h
          exact h
        have hyR : maskSum (m.drop k) R ≠ s - y := by
          intro h
          apply hmsum
          omega
        rw [IHR, if_neg (by rintro ⟨-, h2⟩; exact hyR h2)]
        ring
      · rw [IHL, if_neg (by rintro ⟨-, h2⟩; exact hyL h2)]
        ring
    · -- a length mismatch propagates to one of the halves
      by_cases hmk : k ≤ m.length
      · have : (m.drop k).length ≠ R.length := by
          simp only [List.length_drop, hRlen]
          omega
        rw [IHR, if_neg (by rintro ⟨h1, -⟩; exact this h1)]
        ring
      · have : (m.take k).length ≠ L.length := by
          simp only [List.length_take, hLlen]
          omega
        rw [IHL, if_neg (by rintro ⟨h1, -⟩; exact this h1)]
        ring

/-- Full sampler mass: root capacity draw `s ∝ count S s` over `s ≤ t`,
then the exact-sum split sampler. The capacity appears only here. -/
def samplerMass (S : List ℕ) (t : ℕ) (m : List Bool) : ℚ :=
  ∑ s ∈ range (t + 1), ((count S s : ℕ) : ℚ) / ((countLe S t : ℕ) : ℚ) * splitMass S s m

/-- **The sampler is uniform over knapsack solutions**: every mask of
weight `≤ t` gets probability exactly `1 / countLe S t`; all others `0`. -/
theorem samplerMass_spec (S : List ℕ) (t : ℕ) (m : List Bool) :
    samplerMass S t m =
      if m.length = S.length ∧ maskSum m S ≤ t then ((countLe S t : ℚ))⁻¹ else 0 := by
  unfold samplerMass
  by_cases hm : m.length = S.length ∧ maskSum m S ≤ t
  · obtain ⟨hmlen, hmle⟩ := hm
    rw [if_pos ⟨hmlen, hmle⟩]
    have hcS : 0 < count S (maskSum m S) := count_pos_of_mask S m hmlen
    have hcLe : 0 < countLe S t := by
      have : count S (maskSum m S) ≤ countLe S t := by
        unfold countLe prefixLe
        exact Finset.single_le_sum (f := fun s => count S s)
          (fun i _ => Nat.zero_le _) (by simp [Finset.mem_range]; omega)
      omega
    rw [Finset.sum_eq_single_of_mem (maskSum m S) (by simp [Finset.mem_range]; omega)]
    · rw [splitMass_spec, if_pos ⟨hmlen, rfl⟩]
      have h1 : ((count S (maskSum m S) : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hcS.ne'
      have h2 : ((countLe S t : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hcLe.ne'
      field_simp
    · intro s _ hs
      rw [splitMass_spec, if_neg (by rintro ⟨-, h2⟩; exact hs h2.symm)]
      ring
  · rw [if_neg hm]
    apply Finset.sum_eq_zero
    intro s hs
    rw [Finset.mem_range] at hs
    have : ¬(m.length = S.length ∧ maskSum m S = s) := by
      rintro ⟨h1, h2⟩
      exact hm ⟨h1, by omega⟩
    rw [splitMass_spec, if_neg this]
    ring
