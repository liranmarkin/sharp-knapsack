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

/-! ### A.2: the ∅-split pruning is exact, and the masses form a distribution -/

theorem maskSum_replicate_false (n : ℕ) (S : List ℕ) :
    maskSum (List.replicate n false) S = 0 := by
  induction n generalizing S with
  | zero => simp [maskSum_nil_left]
  | succ n ih =>
    cases S with
    | nil => rfl
    | cons w S => simp [List.replicate_succ, maskSum, ih]

theorem count_zero_pos (S : List ℕ) : 0 < count S 0 := by
  have h := count_pos_of_mask S (List.replicate S.length false) (by simp)
  rwa [maskSum_replicate_false] at h

/-- If the empty set is the only weight-0 subset, the only weight-0 mask is
all-false: the pruned sampler may skip the descent. -/
theorem mask_zero_unique (S : List ℕ) (m : List Bool) (h1 : count S 0 = 1)
    (hlen : m.length = S.length) (hsum : maskSum m S = 0) :
    m = List.replicate S.length false := by
  induction S generalizing m with
  | nil =>
    cases m with
    | nil => rfl
    | cons b m' => simp at hlen
  | cons w S ih =>
    cases m with
    | nil => simp at hlen
    | cons b m' =>
      have hlen' : m'.length = S.length := by simpa using hlen
      have hc : count (w :: S) 0 = count S 0 + (if w = 0 then count S 0 else 0) := by
        rw [count_cons]
        congr 1
        simp only [shiftFun]
        by_cases hw : w = 0
        · subst hw; simp
        · simp [hw]
      have hSpos := count_zero_pos S
      have hw : w ≠ 0 := by
        intro hw0
        subst hw0
        rw [if_pos rfl] at hc
        omega
      have hcS : count S 0 = 1 := by
        rw [if_neg hw] at hc
        omega
      have hb : b = false := by
        cases b with
        | false => rfl
        | true =>
          exfalso
          have : maskSum (true :: m') (w :: S) = w + maskSum m' S := by simp [maskSum]
          omega
      subst hb
      have hsum' : maskSum m' S = 0 := by
        have : maskSum (false :: m') (w :: S) = maskSum m' S := by simp [maskSum]
        omega
      simp [List.replicate_succ, ih m' hcS hlen' hsum']

/-- Closed form of the sampler at a prunable child: the all-false mask with
probability one. -/
theorem splitMass_zero_of_unique (S : List ℕ) (m : List Bool)
    (h1 : count S 0 = 1) :
    splitMass S 0 m = if m = List.replicate S.length false then 1 else 0 := by
  rw [splitMass_spec]
  by_cases hm : m = List.replicate S.length false
  · subst hm
    rw [if_pos ⟨by simp, maskSum_replicate_false _ _⟩, if_pos rfl, h1]
    norm_num
  · rw [if_neg hm]
    rw [if_neg]
    rintro ⟨hlen, hsum⟩
    exact hm (mask_zero_unique S m h1 hlen hsum)

/-- The pruned sampler: identical to `splitMass` except that a child whose
exact weight is `0` and whose weight-0 stratum is only ∅ is emitted as the
all-false mask without descending. -/
def splitMassP (S : List ℕ) (s : ℕ) (m : List Bool) : ℚ :=
  if S.length ≤ 1 then
    if m.length = S.length ∧ maskSum m S = s then ((count S s : ℚ))⁻¹ else 0
  else
    ∑ y ∈ range (s + 1),
      ((count (S.take (S.length / 2)) y * count (S.drop (S.length / 2)) (s - y) : ℕ) : ℚ)
          / ((count S s : ℕ) : ℚ)
        * (if y = 0 ∧ count (S.take (S.length / 2)) 0 = 1 then
             (if m.take (S.length / 2) = List.replicate (S.length / 2) false then 1 else 0)
           else splitMassP (S.take (S.length / 2)) y (m.take (S.length / 2)))
        * (if s - y = 0 ∧ count (S.drop (S.length / 2)) 0 = 1 then
             (if m.drop (S.length / 2) =
                 List.replicate (S.length - S.length / 2) false then 1 else 0)
           else splitMassP (S.drop (S.length / 2)) (s - y) (m.drop (S.length / 2)))
termination_by S.length
decreasing_by
  · simp only [List.length_take]
    omega
  · simp only [List.length_drop]
    omega

/-- **Pruning is exact**: the pruned sampler has the same mass function. -/
theorem splitMassP_eq (S : List ℕ) (s : ℕ) (m : List Bool) :
    splitMassP S s m = splitMass S s m := by
  induction hn : S.length using Nat.strong_induction_on generalizing S s m with
  | _ n IH =>
  subst hn
  rw [splitMassP, splitMass]
  by_cases hlen : S.length ≤ 1
  · rw [if_pos hlen, if_pos hlen]
  rw [if_neg hlen, if_neg hlen]
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  · congr 1
    by_cases hp : y = 0 ∧ count (S.take (S.length / 2)) 0 = 1
    · obtain ⟨hy0, hu⟩ := hp
      rw [if_pos ⟨hy0, hu⟩, hy0, splitMass_zero_of_unique _ _ hu]
      have : (S.take (S.length / 2)).length = S.length / 2 := by
        simp [List.length_take]
        omega
      rw [this]
    · rw [if_neg hp]
      exact IH (S.take (S.length / 2)).length
        (by simp [List.length_take]; omega) _ _ _ rfl
  · by_cases hp : s - y = 0 ∧ count (S.drop (S.length / 2)) 0 = 1
    · obtain ⟨hy0, hu⟩ := hp
      rw [if_pos ⟨hy0, hu⟩, hy0, splitMass_zero_of_unique _ _ hu]
      have : (S.drop (S.length / 2)).length = S.length - S.length / 2 := by
        simp [List.length_drop]
      rw [this]
    · rw [if_neg hp]
      exact IH (S.drop (S.length / 2)).length
        (by simp [List.length_drop]; omega) _ _ _ rfl

/-! The enumeration bridge and totality: the masses sum to one. -/

/-- All Boolean masks of length `n`. -/
def allMasks : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allMasks n).map (List.cons false) ++ (allMasks n).map (List.cons true)

theorem mem_allMasks {n : ℕ} {m : List Bool} (h : m ∈ allMasks n) :
    m.length = n := by
  induction n generalizing m with
  | zero => simp [allMasks] at h; simp [h]
  | succ n ih =>
    simp only [allMasks, List.mem_append, List.mem_map] at h
    rcases h with ⟨m', hm', rfl⟩ | ⟨m', hm', rfl⟩ <;> simp [ih hm']

/-- The enumeration bridge: masks of each weight are counted by `count` -
the trusted specification of the repository. -/
theorem allMasks_countP (S : List ℕ) (s : ℕ) :
    (allMasks S.length).countP (fun m => decide (maskSum m S = s)) = count S s := by
  induction S generalizing s with
  | nil =>
    rcases s with _ | s <;>
      simp [allMasks, count_nil, maskSum]
  | cons w S ih =>
    rw [count_cons]
    show (allMasks (S.length + 1)).countP _ = _
    rw [allMasks, List.countP_append, List.countP_map, List.countP_map]
    have h1 : (allMasks S.length).countP
        ((fun m => decide (maskSum m (w :: S) = s)) ∘ List.cons false) =
        count S s := by
      rw [← ih s]
      apply List.countP_congr
      intro m _
      simp only [Function.comp_apply]
      have hms : maskSum (false :: m) (w :: S) = maskSum m S := by simp [maskSum]
      rw [hms]
    have h2 : (allMasks S.length).countP
        ((fun m => decide (maskSum m (w :: S) = s)) ∘ List.cons true) =
        shiftFun w (count S) s := by
      simp only [shiftFun]
      by_cases hw : w ≤ s
      · rw [if_pos hw, ← ih (s - w)]
        apply List.countP_congr
        intro m _
        simp only [Function.comp_apply]
        have hms : maskSum (true :: m) (w :: S) = w + maskSum m S := by simp [maskSum]
        rw [hms]
        simp only [decide_eq_true_eq]
        omega
      · rw [if_neg hw]
        rw [List.countP_eq_zero]
        intro m _
        simp only [Function.comp_apply]
        have hms : maskSum (true :: m) (w :: S) = w + maskSum m S := by simp [maskSum]
        rw [hms, decide_eq_true_eq]
        omega
    rw [h1, h2]

theorem countLe_pos (S : List ℕ) (t : ℕ) : 0 < countLe S t := by
  have h0 := count_zero_pos S
  have : count S 0 ≤ countLe S t := by
    unfold countLe prefixLe
    exact Finset.single_le_sum (f := fun y => count S y)
      (fun i _ => Nat.zero_le _) (by simp)
  omega

theorem sum_map_ite {α : Type} (l : List α) (p : α → Bool) (c : ℚ) :
    (l.map (fun a => if p a then c else 0)).sum = (l.countP p : ℚ) * c := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases h : p a <;> (simp [h, ih]; try ring)

theorem countP_le_eq_sum {α : Type} (l : List α) (f : α → ℕ) (t : ℕ) :
    l.countP (fun a => decide (f a ≤ t)) =
      ∑ s ∈ range (t + 1), l.countP (fun a => decide (f a = s)) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.countP_cons, ih, Finset.sum_add_distrib]
    congr 1
    by_cases h : f a ≤ t
    · rw [if_pos (by simpa using h)]
      rw [Finset.sum_eq_single_of_mem (f a) (by simp; omega)]
      · simp
      · intro s _ hs
        simp [Ne.symm hs]
    · rw [if_neg (by simpa using h)]
      symm
      apply Finset.sum_eq_zero
      intro s hs
      rw [Finset.mem_range] at hs
      simp
      omega

/-- **Totality**: over all masks, the sampler's masses sum to one - together
with `samplerMass_spec` this states in full that the sampler is exactly the
uniform distribution over the solutions of the #Knapsack instance. -/
theorem samplerMass_total (S : List ℕ) (t : ℕ) :
    ((allMasks S.length).map (samplerMass S t)).sum = 1 := by
  have hmap : (allMasks S.length).map (samplerMass S t) =
      (allMasks S.length).map
        (fun m => if decide (maskSum m S ≤ t) then ((countLe S t : ℚ))⁻¹ else 0) := by
    apply List.map_congr_left
    intro m hm
    rw [samplerMass_spec]
    have hl := mem_allMasks hm
    by_cases h : maskSum m S ≤ t
    · rw [if_pos ⟨hl, h⟩, if_pos (by simpa using h)]
    · rw [if_neg (by rintro ⟨-, h2⟩; exact h h2), if_neg (by simpa using h)]
  rw [hmap, sum_map_ite, countP_le_eq_sum (f := fun m => maskSum m S)]
  simp only [allMasks_countP]
  have hsum : (∑ s ∈ range (t + 1), count S s) = countLe S t := rfl
  rw [hsum]
  have hpos : ((countLe S t : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (countLe_pos S t).ne'
  field_simp
