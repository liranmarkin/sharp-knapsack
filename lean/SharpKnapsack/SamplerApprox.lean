/-
# Stage B of the witness-sampler verification: approximate kernels

The real sampler draws each split not from the exact ratio
`count L y · count R (s−y) / count S s` but from a kernel stored in the
merge arrays. This file proves the *global damage control theorem*: if
every node's kernel is within L1 distance `η` of the exact kernel (and is
a support-faithful probability kernel), the induced distribution over
masks is within L1 distance `η · #internal nodes` of the exact sampler -
which Stage A proved uniform. Stage B.2 (`kernel_l1_of_approx`) bounds the
per-node `η` for kernels arising from multiplicatively-perturbed,
support-restricted arrays - the exact shape produced by the witness
representation (Stage 0).

All statements are finite sums over ℚ; no measure theory.
-/
import SharpKnapsack.SamplerExact

open Finset

/-! ### Masks as a Finset -/

theorem allMasks_mem_of_length {n : ℕ} {m : List Bool} (h : m.length = n) :
    m ∈ allMasks n := by
  induction n generalizing m with
  | zero =>
    cases m with
    | nil => simp [allMasks]
    | cons b m' => simp at h
  | succ n ih =>
    cases m with
    | nil => simp at h
    | cons b m' =>
      have h' : m'.length = n := by simpa using h
      simp only [allMasks, List.mem_append, List.mem_map]
      cases b with
      | false => exact Or.inl ⟨m', ih h', rfl⟩
      | true => exact Or.inr ⟨m', ih h', rfl⟩

theorem allMasks_nodup (n : ℕ) : (allMasks n).Nodup := by
  induction n with
  | zero => simp [allMasks]
  | succ n ih =>
    simp only [allMasks]
    refine List.Nodup.append ?_ ?_ ?_
    · exact ih.map (fun a b h => by simpa using h)
    · exact ih.map (fun a b h => by simpa using h)
    · intro x hx hy
      simp only [List.mem_map] at hx hy
      obtain ⟨a, -, rfl⟩ := hx
      obtain ⟨b, -, hb⟩ := hy
      simp at hb

/-- The Finset of all masks of length `n`. -/
def maskFinset (n : ℕ) : Finset (List Bool) := (allMasks n).toFinset

theorem mem_maskFinset {n : ℕ} {m : List Bool} :
    m ∈ maskFinset n ↔ m.length = n := by
  constructor
  · intro h
    exact mem_allMasks (by simpa [maskFinset] using h)
  · intro h
    simp [maskFinset]
    exact allMasks_mem_of_length h

theorem sum_maskFinset_eq_list {n : ℕ} (f : List Bool → ℚ) :
    ∑ m ∈ maskFinset n, f m = ((allMasks n).map f).sum := by
  rw [maskFinset, List.sum_toFinset _ (allMasks_nodup n)]

/-- Sums over masks of length `k + j` split as double sums over the halves. -/
theorem sum_maskFinset_split (k j : ℕ) (F : List Bool → ℚ) :
    ∑ m ∈ maskFinset (k + j), F m =
      ∑ p ∈ maskFinset k ×ˢ maskFinset j, F (p.1 ++ p.2) := by
  apply Finset.sum_nbij' (i := fun m => (m.take k, m.drop k))
    (j := fun p => p.1 ++ p.2)
  · intro m hm
    rw [mem_maskFinset] at hm
    rw [Finset.mem_product, mem_maskFinset, mem_maskFinset]
    constructor
    · simp [List.length_take]
      omega
    · simp [List.length_drop, hm]
  · intro p hp
    rw [Finset.mem_product, mem_maskFinset, mem_maskFinset] at hp
    rw [mem_maskFinset]
    simp [hp.1, hp.2]
  · intro m _
    exact List.take_append_drop k m
  · intro p hp
    rw [Finset.mem_product, mem_maskFinset, mem_maskFinset] at hp
    have h1 : (p.1 ++ p.2).take k = p.1 := by
      rw [← hp.1]
      exact List.take_left
    have h2 : (p.1 ++ p.2).drop k = p.2 := by
      rw [← hp.1]
      exact List.drop_left
    exact Prod.ext h1 h2
  · intro m _
    rw [List.take_append_drop]

/-- Indicator sums over masks reduce to `count` (Finset form of the
enumeration bridge). -/
theorem sum_maskFinset_indicator (S : List ℕ) (s : ℕ) (c : ℚ) :
    (∑ m ∈ maskFinset S.length,
      if m.length = S.length ∧ maskSum m S = s then c else 0) =
      (count S s : ℚ) * c := by
  rw [sum_maskFinset_eq_list]
  have hmap : (allMasks S.length).map
      (fun m => if m.length = S.length ∧ maskSum m S = s then c else 0) =
      (allMasks S.length).map
      (fun m => if decide (maskSum m S = s) then c else 0) := by
    apply List.map_congr_left
    intro m hm
    have hl := mem_allMasks hm
    by_cases h : maskSum m S = s
    · rw [if_pos ⟨hl, h⟩, if_pos (by simpa using h)]
    · rw [if_neg (by rintro ⟨-, h2⟩; exact h h2), if_neg (by simpa using h)]
  rw [hmap, sum_map_ite, allMasks_countP]

/-- Stage A's uniformity, restated as a Finset total. -/
theorem sum_maskFinset_splitMass (S : List ℕ) (s : ℕ) (hc : count S s ≠ 0) :
    ∑ m ∈ maskFinset S.length, splitMass S s m = 1 := by
  have h : ∀ m ∈ maskFinset S.length, splitMass S s m =
      if m.length = S.length ∧ maskSum m S = s then ((count S s : ℚ))⁻¹ else 0 :=
    fun m _ => splitMass_spec S s m
  rw [Finset.sum_congr rfl h, sum_maskFinset_indicator]
  have : ((count S s : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hc
  field_simp

/-! ### The kernel-parametrized sampler -/

/-- The exact split kernel of Stage A. -/
def exactKernel (S : List ℕ) (s : ℕ) (y : ℕ) : ℚ :=
  ((count (S.take (S.length / 2)) y * count (S.drop (S.length / 2)) (s - y) : ℕ) : ℚ)
    / ((count S s : ℕ) : ℚ)

/-- Lemma 10 in kernel form: the exact kernel is a probability kernel. -/
theorem exactKernel_total (S : List ℕ) (s : ℕ) (hc : count S s ≠ 0) :
    ∑ y ∈ range (s + 1), exactKernel S s y = 1 := by
  have hconv : count S s =
      ∑ y ∈ range (s + 1),
        count (S.take (S.length / 2)) y * count (S.drop (S.length / 2)) (s - y) := by
    conv_lhs => rw [← List.take_append_drop (S.length / 2) S]
    rw [count_append]
    rfl
  unfold exactKernel
  rw [← Finset.sum_div]
  rw [show (∑ y ∈ range (s + 1),
      ((count (S.take (S.length / 2)) y * count (S.drop (S.length / 2)) (s - y) : ℕ) : ℚ)) =
      ((count S s : ℕ) : ℚ) by push_cast [hconv]; ring]
  have : ((count S s : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hc
  field_simp

/-- The sampler driven by an arbitrary split kernel `Q` (the stored-array
kernel of the real algorithm). Leaves are exact table draws, as in the
algorithm. -/
def splitMassK (Q : List ℕ → ℕ → ℕ → ℚ) (S : List ℕ) (s : ℕ) (m : List Bool) : ℚ :=
  if S.length ≤ 1 then
    if m.length = S.length ∧ maskSum m S = s then ((count S s : ℚ))⁻¹ else 0
  else
    ∑ y ∈ range (s + 1),
      Q S s y
        * splitMassK Q (S.take (S.length / 2)) y (m.take (S.length / 2))
        * splitMassK Q (S.drop (S.length / 2)) (s - y) (m.drop (S.length / 2))
termination_by S.length
decreasing_by
  · simp only [List.length_take]
    omega
  · simp only [List.length_drop]
    omega

/-- With the exact kernel, the parametrized sampler is Stage A's sampler. -/
theorem splitMassK_exact (S : List ℕ) (s : ℕ) (m : List Bool) :
    splitMassK exactKernel S s m = splitMass S s m := by
  induction hn : S.length using Nat.strong_induction_on generalizing S s m with
  | _ n IH =>
  subst hn
  rw [splitMassK, splitMass]
  by_cases hlen : S.length ≤ 1
  · rw [if_pos hlen, if_pos hlen]
  rw [if_neg hlen, if_neg hlen]
  apply Finset.sum_congr rfl
  intro y _
  rw [IH (S.take (S.length / 2)).length (by simp [List.length_take]; omega) _ _ _ rfl,
    IH (S.drop (S.length / 2)).length (by simp [List.length_drop]; omega) _ _ _ rfl]
  rfl

/-- Number of internal nodes of the recursion tree - the budget unit of the
damage-control theorem. -/
def internalNodes (S : List ℕ) : ℕ :=
  if S.length ≤ 1 then 0
  else 1 + internalNodes (S.take (S.length / 2)) + internalNodes (S.drop (S.length / 2))
termination_by S.length
decreasing_by
  · simp only [List.length_take]
    omega
  · simp only [List.length_drop]
    omega

/-- Hypotheses on a stored kernel: nonnegative, support-faithful (it never
invents splits the exact counts forbid - which the witness representation
guarantees, since stored values are sums of true products), and a
probability kernel wherever the node is reachable. -/
structure KernelOK (Q : List ℕ → ℕ → ℕ → ℚ) : Prop where
  nonneg : ∀ S s y, 0 ≤ Q S s y
  total : ∀ S s, count S s ≠ 0 → ∑ y ∈ range (s + 1), Q S s y = 1
  supp : ∀ S s y, y ≤ s → Q S s y ≠ 0 →
    count (S.take (S.length / 2)) y ≠ 0 ∧ count (S.drop (S.length / 2)) (s - y) ≠ 0

/-- Totality of the kernel sampler at reachable nodes. -/
theorem splitMassK_total (Q : List ℕ → ℕ → ℕ → ℚ) (hQ : KernelOK Q)
    (S : List ℕ) (s : ℕ) :
    count S s ≠ 0 → ∑ m ∈ maskFinset S.length, splitMassK Q S s m = 1 := by
  induction hn : S.length using Nat.strong_induction_on generalizing S s with
  | _ n IH =>
  intro hc
  subst hn
  by_cases hlen : S.length ≤ 1
  · have h : ∀ m ∈ maskFinset S.length, splitMassK Q S s m =
        if m.length = S.length ∧ maskSum m S = s then ((count S s : ℚ))⁻¹ else 0 := by
      intro m _
      rw [splitMassK, if_pos hlen]
    rw [Finset.sum_congr rfl h, sum_maskFinset_indicator]
    have : ((count S s : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hc
    field_simp
  · set k := S.length / 2 with hk
    have hsplitlen : S.length = k + (S.length - k) := by omega
    have h : ∀ m ∈ maskFinset S.length, splitMassK Q S s m =
        ∑ y ∈ range (s + 1), Q S s y
          * splitMassK Q (S.take k) y (m.take k)
          * splitMassK Q (S.drop k) (s - y) (m.drop k) := by
      intro m _
      rw [splitMassK, if_neg hlen]
    rw [Finset.sum_congr rfl h]
    rw [hsplitlen, sum_maskFinset_split k (S.length - k)]
    have h2 : ∀ p ∈ maskFinset k ×ˢ maskFinset (S.length - k),
        (∑ y ∈ range (s + 1), Q S s y
          * splitMassK Q (S.take k) y ((p.1 ++ p.2).take k)
          * splitMassK Q (S.drop k) (s - y) ((p.1 ++ p.2).drop k)) =
        ∑ y ∈ range (s + 1), Q S s y
          * splitMassK Q (S.take k) y p.1
          * splitMassK Q (S.drop k) (s - y) p.2 := by
      intro p hp
      rw [Finset.mem_product, mem_maskFinset, mem_maskFinset] at hp
      have e1 : (p.1 ++ p.2).take k = p.1 := by
        rw [← hp.1]
        exact List.take_left
      have e2 : (p.1 ++ p.2).drop k = p.2 := by
        rw [← hp.1]
        exact List.drop_left
      rw [e1, e2]
    rw [Finset.sum_congr rfl h2, Finset.sum_comm]
    have h3 : ∀ y ∈ range (s + 1),
        (∑ p ∈ maskFinset k ×ˢ maskFinset (S.length - k),
          Q S s y * splitMassK Q (S.take k) y p.1
            * splitMassK Q (S.drop k) (s - y) p.2) = Q S s y := by
      intro y hy
      rw [Finset.mem_range] at hy
      by_cases hq : Q S s y = 0
      · rw [hq]
        simp
      · obtain ⟨hcL, hcR⟩ := hQ.supp S s y (by omega) hq
        have hLl : (S.take k).length = k := by
          simp [List.length_take]
          omega
        have hRl : (S.drop k).length = S.length - k := by
          simp [List.length_drop]
        have hL := IH (S.take k).length (by omega) _ y rfl hcL
        have hR := IH (S.drop k).length (by rw [hRl]; omega) _ (s - y) rfl hcR
        rw [hLl] at hL
        rw [hRl] at hR
        calc ∑ p ∈ maskFinset k ×ˢ maskFinset (S.length - k),
              Q S s y * splitMassK Q (S.take k) y p.1
                * splitMassK Q (S.drop k) (s - y) p.2
            = Q S s y * ((∑ a ∈ maskFinset k, splitMassK Q (S.take k) y a) *
                (∑ b ∈ maskFinset (S.length - k), splitMassK Q (S.drop k) (s - y) b)) := by
              rw [Finset.sum_product, Finset.sum_mul_sum, Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro a _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro b _
              ring
          _ = Q S s y := by
              rw [hL, hR]
              ring
    rw [Finset.sum_congr rfl h3]
    exact hQ.total S s hc

/-! ### The damage-control theorem -/

theorem exactKernel_nonneg (S : List ℕ) (s y : ℕ) : 0 ≤ exactKernel S s y := by
  unfold exactKernel
  positivity

theorem exactKernel_supp (S : List ℕ) (s y : ℕ) (h : exactKernel S s y ≠ 0) :
    count (S.take (S.length / 2)) y ≠ 0 ∧
      count (S.drop (S.length / 2)) (s - y) ≠ 0 := by
  constructor
  · intro h0
    apply h
    unfold exactKernel
    rw [h0]
    norm_num
  · intro h0
    apply h
    unfold exactKernel
    rw [h0]
    norm_num

theorem splitMassK_nonneg (Q : List ℕ → ℕ → ℕ → ℚ)
    (hnn : ∀ S s y, 0 ≤ Q S s y) (S : List ℕ) (s : ℕ) (m : List Bool) :
    0 ≤ splitMassK Q S s m := by
  induction hn : S.length using Nat.strong_induction_on generalizing S s m with
  | _ n IH =>
  subst hn
  rw [splitMassK]
  by_cases hlen : S.length ≤ 1
  · rw [if_pos hlen]
    split <;> positivity
  · rw [if_neg hlen]
    apply Finset.sum_nonneg
    intro y _
    have h1 := IH (S.take (S.length / 2)).length
      (by simp [List.length_take]; omega) (S.take (S.length / 2)) y
      (m.take (S.length / 2)) rfl
    have h2 := IH (S.drop (S.length / 2)).length
      (by simp [List.length_drop]; omega) (S.drop (S.length / 2)) (s - y)
      (m.drop (S.length / 2)) rfl
    have h3 := hnn S s y
    positivity

theorem splitMass_nonneg (S : List ℕ) (s : ℕ) (m : List Bool) :
    0 ≤ splitMass S s m := by
  rw [← splitMassK_exact]
  exact splitMassK_nonneg exactKernel (fun S s y => exactKernel_nonneg S s y) S s m

/-- Pointwise hybrid bound for one summand of the chain rule. -/
theorem hybrid_abs (q e aL bL aR' bR' : ℚ)
    (haL : 0 ≤ aL) (haR : 0 ≤ aR') (hbL : 0 ≤ bL) (he : 0 ≤ e) :
    |q * aL * aR' - e * bL * bR'| ≤
      |q - e| * aL * aR' + e * |aL - bL| * aR' + e * bL * |aR' - bR'| := by
  have hid : q * aL * aR' - e * bL * bR' =
      (q - e) * aL * aR' + e * (aL - bL) * aR' + e * bL * (aR' - bR') := by
    ring
  rw [hid]
  refine le_trans (abs_add_three _ _ _) ?_
  refine add_le_add (add_le_add ?_ ?_) ?_
  · exact le_of_eq (by rw [abs_mul, abs_mul, abs_of_nonneg haL, abs_of_nonneg haR])
  · exact le_of_eq (by rw [abs_mul, abs_mul, abs_of_nonneg he, abs_of_nonneg haR])
  · exact le_of_eq (by rw [abs_mul, abs_mul, abs_of_nonneg he, abs_of_nonneg hbL])

/-- Product sums over mask pairs factorize. -/
theorem sum_product_factor (A B : Finset (List Bool)) (c : ℚ)
    (f g : List Bool → ℚ) :
    ∑ p ∈ A ×ˢ B, c * f p.1 * g p.2 = c * (∑ a ∈ A, f a) * (∑ b ∈ B, g b) := by
  rw [Finset.sum_product]
  have h : ∀ a ∈ A, (∑ b ∈ B, c * f a * g b) = c * f a * ∑ b ∈ B, g b :=
    fun a _ => by rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl h, ← Finset.sum_mul, ← Finset.mul_sum]

/-- **The damage-control theorem (Stage B.1)**: if every node's stored
kernel is within L1 distance `η` of the exact kernel, the sampler's output
distribution is within L1 distance `η · #internal nodes` of the exact
(uniform) sampler. Approximation error only accumulates additively, once
per merge - the formal counterpart of the TV accounting in
`docs/witness-sampler.md`. -/
theorem splitMassK_l1 (Q : List ℕ → ℕ → ℕ → ℚ) (hQ : KernelOK Q) (η : ℚ)
    (hloc : ∀ S s, count S s ≠ 0 →
      ∑ y ∈ range (s + 1), |Q S s y - exactKernel S s y| ≤ η)
    (S : List ℕ) (s : ℕ) :
    count S s ≠ 0 →
    ∑ m ∈ maskFinset S.length, |splitMassK Q S s m - splitMass S s m| ≤
      η * internalNodes S := by
  induction hn : S.length using Nat.strong_induction_on generalizing S s with
  | _ n IH =>
  intro hc
  subst hn
  have hη : 0 ≤ η :=
    le_trans (Finset.sum_nonneg fun y _ => abs_nonneg _) (hloc S s hc)
  by_cases hlen : S.length ≤ 1
  · have h : ∀ m ∈ maskFinset S.length,
        |splitMassK Q S s m - splitMass S s m| = 0 := by
      intro m _
      rw [splitMassK, splitMass, if_pos hlen, if_pos hlen]
      simp
    rw [Finset.sum_congr rfl h]
    simp [internalNodes, hlen]
  · set k := S.length / 2 with hk
    set L := S.take k with hL
    set R := S.drop k with hR
    have hLl : L.length = k := by
      simp [hL, List.length_take]
      omega
    have hRl : R.length = S.length - k := by
      simp [hR, List.length_drop]
    have hsplitlen : S.length = k + (S.length - k) := by omega
    -- unfold both samplers and split the mask sum over the halves
    have hbody : ∀ m ∈ maskFinset S.length,
        |splitMassK Q S s m - splitMass S s m| =
        |∑ y ∈ range (s + 1),
          (Q S s y * splitMassK Q L y (m.take k) * splitMassK Q R (s - y) (m.drop k)
            - exactKernel S s y * splitMass L y (m.take k) * splitMass R (s - y) (m.drop k))| := by
      intro m _
      rw [splitMassK, splitMass, if_neg hlen, if_neg hlen, ← Finset.sum_sub_distrib]
      rfl
    rw [Finset.sum_congr rfl hbody]
    rw [hsplitlen, sum_maskFinset_split k (S.length - k)]
    have hbody2 : ∀ p ∈ maskFinset k ×ˢ maskFinset (S.length - k),
        |∑ y ∈ range (s + 1),
          (Q S s y * splitMassK Q L y ((p.1 ++ p.2).take k)
              * splitMassK Q R (s - y) ((p.1 ++ p.2).drop k)
            - exactKernel S s y * splitMass L y ((p.1 ++ p.2).take k)
              * splitMass R (s - y) ((p.1 ++ p.2).drop k))| =
        |∑ y ∈ range (s + 1),
          (Q S s y * splitMassK Q L y p.1 * splitMassK Q R (s - y) p.2
            - exactKernel S s y * splitMass L y p.1 * splitMass R (s - y) p.2)| := by
      intro p hp
      rw [Finset.mem_product, mem_maskFinset, mem_maskFinset] at hp
      have e1 : (p.1 ++ p.2).take k = p.1 := by
        rw [← hp.1]
        exact List.take_left
      have e2 : (p.1 ++ p.2).drop k = p.2 := by
        rw [← hp.1]
        exact List.drop_left
      rw [e1, e2]
    rw [Finset.sum_congr rfl hbody2]
    -- move the absolute value inside, swap the sums
    have hstep1 :
        (∑ p ∈ maskFinset k ×ˢ maskFinset (S.length - k),
          |∑ y ∈ range (s + 1),
            (Q S s y * splitMassK Q L y p.1 * splitMassK Q R (s - y) p.2
              - exactKernel S s y * splitMass L y p.1 * splitMass R (s - y) p.2)|) ≤
        ∑ y ∈ range (s + 1), ∑ p ∈ maskFinset k ×ˢ maskFinset (S.length - k),
          |Q S s y * splitMassK Q L y p.1 * splitMassK Q R (s - y) p.2
            - exactKernel S s y * splitMass L y p.1 * splitMass R (s - y) p.2| := by
      rw [Finset.sum_comm]
      exact Finset.sum_le_sum fun p _ => Finset.abs_sum_le_sum_abs _ _
    refine le_trans hstep1 ?_
    -- bound each y-slice by the three hybrid terms and dispatch by case
    have hslice : ∀ y ∈ range (s + 1),
        (∑ p ∈ maskFinset k ×ˢ maskFinset (S.length - k),
          |Q S s y * splitMassK Q L y p.1 * splitMassK Q R (s - y) p.2
            - exactKernel S s y * splitMass L y p.1 * splitMass R (s - y) p.2|) ≤
        |Q S s y - exactKernel S s y|
          + exactKernel S s y * (η * internalNodes L)
          + exactKernel S s y * (η * internalNodes R) := by
      intro y hy
      rw [Finset.mem_range] at hy
      by_cases hzero : Q S s y = 0 ∧ exactKernel S s y = 0
      · obtain ⟨hq0, he0⟩ := hzero
        have h : ∀ p ∈ maskFinset k ×ˢ maskFinset (S.length - k),
            |Q S s y * splitMassK Q L y p.1 * splitMassK Q R (s - y) p.2
              - exactKernel S s y * splitMass L y p.1 * splitMass R (s - y) p.2| = 0 := by
          intro p _
          rw [hq0, he0]
          simp
        rw [Finset.sum_congr rfl h]
        simp [hq0, he0]
      · have hcounts : count L y ≠ 0 ∧ count R (s - y) ≠ 0 := by
          by_cases hq : Q S s y = 0
          · have he : exactKernel S s y ≠ 0 := fun he => hzero ⟨hq, he⟩
            have h := exactKernel_supp S s y he
            rw [← hk, ← hL, ← hR] at h
            exact h
          · have h := hQ.supp S s y (by omega) hq
            rw [← hk, ← hL, ← hR] at h
            exact h
        obtain ⟨hcL, hcR⟩ := hcounts
        have hAL : ∑ a ∈ maskFinset k, splitMassK Q L y a = 1 := by
          have h := splitMassK_total Q hQ L y hcL
          rwa [hLl] at h
        have hAR : ∑ b ∈ maskFinset (S.length - k), splitMassK Q R (s - y) b = 1 := by
          have h := splitMassK_total Q hQ R (s - y) hcR
          rwa [hRl] at h
        have hBL : ∑ a ∈ maskFinset k, splitMass L y a = 1 := by
          have h := sum_maskFinset_splitMass L y hcL
          rwa [hLl] at h
        have hIHL : (∑ a ∈ maskFinset k,
            |splitMassK Q L y a - splitMass L y a|) ≤ η * internalNodes L := by
          have h := IH L.length (by omega) L y rfl hcL
          rwa [hLl] at h
        have hIHR : (∑ b ∈ maskFinset (S.length - k),
            |splitMassK Q R (s - y) b - splitMass R (s - y) b|) ≤
            η * internalNodes R := by
          have h := IH R.length (by omega) R (s - y) rfl hcR
          rwa [hRl] at h
        have hpoint : ∀ p ∈ maskFinset k ×ˢ maskFinset (S.length - k),
            |Q S s y * splitMassK Q L y p.1 * splitMassK Q R (s - y) p.2
              - exactKernel S s y * splitMass L y p.1 * splitMass R (s - y) p.2| ≤
            |Q S s y - exactKernel S s y| * splitMassK Q L y p.1
                * splitMassK Q R (s - y) p.2
              + exactKernel S s y * |splitMassK Q L y p.1 - splitMass L y p.1|
                * splitMassK Q R (s - y) p.2
              + exactKernel S s y * splitMass L y p.1
                * |splitMassK Q R (s - y) p.2 - splitMass R (s - y) p.2| := by
          intro p _
          exact hybrid_abs _ _ _ _ _ _
            (splitMassK_nonneg Q hQ.nonneg L y p.1)
            (splitMassK_nonneg Q hQ.nonneg R (s - y) p.2)
            (splitMass_nonneg L y p.1)
            (exactKernel_nonneg S s y)
        refine le_trans (Finset.sum_le_sum hpoint) ?_
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        have hT1 : (∑ p ∈ maskFinset k ×ˢ maskFinset (S.length - k),
            |Q S s y - exactKernel S s y| * splitMassK Q L y p.1
              * splitMassK Q R (s - y) p.2) = |Q S s y - exactKernel S s y| := by
          rw [sum_product_factor, hAL, hAR]
          ring
        have hT2 : (∑ p ∈ maskFinset k ×ˢ maskFinset (S.length - k),
            exactKernel S s y * |splitMassK Q L y p.1 - splitMass L y p.1|
              * splitMassK Q R (s - y) p.2) ≤
            exactKernel S s y * (η * internalNodes L) := by
          rw [Finset.sum_product]
          have hinner : ∀ a ∈ maskFinset k,
              (∑ b ∈ maskFinset (S.length - k),
                exactKernel S s y * |splitMassK Q L y a - splitMass L y a|
                  * splitMassK Q R (s - y) b) =
              exactKernel S s y * |splitMassK Q L y a - splitMass L y a| := by
            intro a _
            rw [← Finset.mul_sum, hAR, mul_one]
          rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum]
          exact mul_le_mul_of_nonneg_left hIHL (exactKernel_nonneg S s y)
        have hT3 : (∑ p ∈ maskFinset k ×ˢ maskFinset (S.length - k),
            exactKernel S s y * splitMass L y p.1
              * |splitMassK Q R (s - y) p.2 - splitMass R (s - y) p.2|) ≤
            exactKernel S s y * (η * internalNodes R) := by
          rw [Finset.sum_product]
          have hinner : ∀ a ∈ maskFinset k,
              (∑ b ∈ maskFinset (S.length - k),
                exactKernel S s y * splitMass L y a
                  * |splitMassK Q R (s - y) b - splitMass R (s - y) b|) =
              exactKernel S s y * splitMass L y a
                * (∑ b ∈ maskFinset (S.length - k),
                    |splitMassK Q R (s - y) b - splitMass R (s - y) b|) := by
            intro a _
            rw [Finset.mul_sum]
          rw [Finset.sum_congr rfl hinner, ← Finset.sum_mul, ← Finset.mul_sum, hBL,
            mul_one]
          exact mul_le_mul_of_nonneg_left hIHR (exactKernel_nonneg S s y)
        exact add_le_add (add_le_add (le_of_eq hT1) hT2) hT3
    refine le_trans (Finset.sum_le_sum hslice) ?_
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    have hA : (∑ y ∈ range (s + 1), |Q S s y - exactKernel S s y|) ≤ η :=
      hloc S s hc
    have hB : (∑ y ∈ range (s + 1),
        exactKernel S s y * (η * internalNodes L)) = η * internalNodes L := by
      rw [← Finset.sum_mul, exactKernel_total S s hc, one_mul]
    have hC : (∑ y ∈ range (s + 1),
        exactKernel S s y * (η * internalNodes R)) = η * internalNodes R := by
      rw [← Finset.sum_mul, exactKernel_total S s hc, one_mul]
    have hnode : ((internalNodes S : ℕ) : ℚ) =
        1 + internalNodes L + internalNodes R := by
      rw [internalNodes, if_neg hlen]
      rw [← hk, ← hL, ← hR]
      push_cast
      ring
    calc (∑ y ∈ range (s + 1), |Q S s y - exactKernel S s y|)
          + (∑ y ∈ range (s + 1), exactKernel S s y * (η * internalNodes L))
          + (∑ y ∈ range (s + 1), exactKernel S s y * (η * internalNodes R))
        ≤ η + η * internalNodes L + η * internalNodes R := by
          rw [hB, hC]
          exact add_le_add (add_le_add hA le_rfl) le_rfl
      _ = η * internalNodes S := by
          rw [hnode]
          ring

/-! ### The root layer -/

/-- Exact root kernel: the capacity draw of Stage A. -/
def exactRootKernel (S : List ℕ) (t : ℕ) (s : ℕ) : ℚ :=
  ((count S s : ℕ) : ℚ) / ((countLe S t : ℕ) : ℚ)

theorem exactRootKernel_total (S : List ℕ) (t : ℕ) :
    ∑ s ∈ range (t + 1), exactRootKernel S t s = 1 := by
  unfold exactRootKernel
  rw [← Finset.sum_div]
  have hsum : (∑ s ∈ range (t + 1), ((count S s : ℕ) : ℚ)) =
      ((countLe S t : ℕ) : ℚ) := by
    have : countLe S t = ∑ s ∈ range (t + 1), count S s := rfl
    rw [this]
    push_cast
    ring
  rw [hsum]
  have : ((countLe S t : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (countLe_pos S t).ne'
  field_simp

theorem exactRootKernel_nonneg (S : List ℕ) (t s : ℕ) :
    0 ≤ exactRootKernel S t s := by
  unfold exactRootKernel
  positivity

theorem exactRootKernel_supp (S : List ℕ) (t s : ℕ)
    (h : exactRootKernel S t s ≠ 0) : count S s ≠ 0 := by
  intro h0
  apply h
  unfold exactRootKernel
  rw [h0]
  norm_num

/-- The full sampler with a stored root kernel and stored split kernels. -/
def samplerMassK (Q₀ : ℕ → ℚ) (Q : List ℕ → ℕ → ℕ → ℚ)
    (S : List ℕ) (t : ℕ) (m : List Bool) : ℚ :=
  ∑ s ∈ range (t + 1), Q₀ s * splitMassK Q S s m

theorem hybrid_abs2 (q e a b : ℚ) (ha : 0 ≤ a) (he : 0 ≤ e) :
    |q * a - e * b| ≤ |q - e| * a + e * |a - b| := by
  have hid : q * a - e * b = (q - e) * a + e * (a - b) := by ring
  rw [hid]
  refine le_trans (abs_add_le _ _) (add_le_add ?_ ?_)
  · exact le_of_eq (by rw [abs_mul, abs_of_nonneg ha])
  · exact le_of_eq (by rw [abs_mul, abs_of_nonneg he])

/-- **Stage B.1, assembled**: root-kernel error `η₀` plus `η` per internal
node bounds the L1 distance of the full stored-kernel sampler from the
exactly-uniform sampler of Stage A. -/
theorem samplerMassK_l1 (Q₀ : ℕ → ℚ) (Q : List ℕ → ℕ → ℕ → ℚ) (hQ : KernelOK Q)
    (S : List ℕ) (t : ℕ) (η₀ η : ℚ)
    (_hQ₀nn : ∀ s, 0 ≤ Q₀ s)
    (hQ₀supp : ∀ s, s ≤ t → Q₀ s ≠ 0 → count S s ≠ 0)
    (hloc0 : (∑ s ∈ range (t + 1), |Q₀ s - exactRootKernel S t s|) ≤ η₀)
    (hloc : ∀ S' s', count S' s' ≠ 0 →
      ∑ y ∈ range (s' + 1), |Q S' s' y - exactKernel S' s' y| ≤ η) :
    (∑ m ∈ maskFinset S.length, |samplerMassK Q₀ Q S t m - samplerMass S t m|) ≤
      η₀ + η * internalNodes S := by
  have hη : 0 ≤ η := by
    have h := hloc S 0 (by have := count_zero_pos S; omega)
    exact le_trans (Finset.sum_nonneg fun y _ => abs_nonneg _) h
  have hbody : ∀ m ∈ maskFinset S.length,
      |samplerMassK Q₀ Q S t m - samplerMass S t m| =
      |∑ s ∈ range (t + 1),
        (Q₀ s * splitMassK Q S s m - exactRootKernel S t s * splitMass S s m)| := by
    intro m _
    unfold samplerMassK samplerMass
    rw [← Finset.sum_sub_distrib]
    rfl
  rw [Finset.sum_congr rfl hbody]
  have hstep1 :
      (∑ m ∈ maskFinset S.length,
        |∑ s ∈ range (t + 1),
          (Q₀ s * splitMassK Q S s m - exactRootKernel S t s * splitMass S s m)|) ≤
      ∑ s ∈ range (t + 1), ∑ m ∈ maskFinset S.length,
        |Q₀ s * splitMassK Q S s m - exactRootKernel S t s * splitMass S s m| := by
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum fun m _ => Finset.abs_sum_le_sum_abs _ _
  refine le_trans hstep1 ?_
  have hslice : ∀ s ∈ range (t + 1),
      (∑ m ∈ maskFinset S.length,
        |Q₀ s * splitMassK Q S s m - exactRootKernel S t s * splitMass S s m|) ≤
      |Q₀ s - exactRootKernel S t s|
        + exactRootKernel S t s * (η * internalNodes S) := by
    intro s hs
    rw [Finset.mem_range] at hs
    by_cases hzero : Q₀ s = 0 ∧ exactRootKernel S t s = 0
    · obtain ⟨hq0, he0⟩ := hzero
      have h : ∀ m ∈ maskFinset S.length,
          |Q₀ s * splitMassK Q S s m - exactRootKernel S t s * splitMass S s m| = 0 := by
        intro m _
        rw [hq0, he0]
        simp
      rw [Finset.sum_congr rfl h]
      simp [hq0, he0]
    · have hc : count S s ≠ 0 := by
        by_cases hq : Q₀ s = 0
        · exact exactRootKernel_supp S t s (fun he => hzero ⟨hq, he⟩)
        · exact hQ₀supp s (by omega) hq
      have hA : ∑ m ∈ maskFinset S.length, splitMassK Q S s m = 1 :=
        splitMassK_total Q hQ S s hc
      have hIH : (∑ m ∈ maskFinset S.length,
          |splitMassK Q S s m - splitMass S s m|) ≤ η * internalNodes S :=
        splitMassK_l1 Q hQ η hloc S s hc
      have hpoint : ∀ m ∈ maskFinset S.length,
          |Q₀ s * splitMassK Q S s m - exactRootKernel S t s * splitMass S s m| ≤
          |Q₀ s - exactRootKernel S t s| * splitMassK Q S s m
            + exactRootKernel S t s * |splitMassK Q S s m - splitMass S s m| := by
        intro m _
        exact hybrid_abs2 _ _ _ _
          (splitMassK_nonneg Q hQ.nonneg S s m)
          (exactRootKernel_nonneg S t s)
      refine le_trans (Finset.sum_le_sum hpoint) ?_
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hA, mul_one]
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hIH (exactRootKernel_nonneg S t s))
  refine le_trans (Finset.sum_le_sum hslice) ?_
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, exactRootKernel_total S t, one_mul]
  exact add_le_add hloc0 le_rfl

/-! ### Stage B.2: the local kernel bound

A stored kernel is the normalization of `r`, a multiplicatively
`(1±δ)`-perturbed copy of the exact weights `b` restricted to a witness set
`W` that carries all but a `γ`-fraction of the mass (Stage 0's diagonal
domination provides exactly this shape). Its L1 distance from the exact
kernel is at most `4δ + 3γ` - the `η` fed to the damage-control theorem. -/
theorem kernel_l1_of_approx (n : ℕ) (b r : ℕ → ℚ) (W : Finset ℕ)
    (hW : W ⊆ range n) (δ γ : ℚ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 4) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1 / 4)
    (hb : ∀ y ∈ range n, 0 ≤ b y)
    (hr0 : ∀ y ∈ range n, y ∉ W → r y = 0)
    (hrl : ∀ y ∈ W, (1 - δ) * b y ≤ r y)
    (hru : ∀ y ∈ W, r y ≤ (1 + δ) * b y)
    (hdrop : (∑ y ∈ range n \ W, b y) ≤ γ * ∑ y ∈ range n, b y)
    (hBpos : 0 < ∑ y ∈ range n, b y) :
    (∑ y ∈ range n,
      |r y / (∑ z ∈ range n, r z) - b y / (∑ z ∈ range n, b z)|) ≤
      4 * δ + 3 * γ := by
  set B := ∑ y ∈ range n, b y with hB
  set R := ∑ y ∈ range n, r y with hR
  have hbW : ∀ y ∈ W, 0 ≤ b y := fun y hy => hb y (hW hy)
  have hRW : R = ∑ y ∈ W, r y := by
    rw [hR]
    exact (Finset.sum_subset hW hr0).symm
  have hWB : (∑ y ∈ W, b y) = B - ∑ y ∈ range n \ W, b y := by
    have h := Finset.sum_sdiff (f := b) hW
    rw [hB]
    linarith
  have hWBle : (∑ y ∈ W, b y) ≤ B := by
    have hd : 0 ≤ ∑ y ∈ range n \ W, b y :=
      Finset.sum_nonneg fun y hy => hb y (Finset.mem_sdiff.mp hy).1
    linarith [hWB]
  have hRlow : (1 - δ) * ((1 - γ) * B) ≤ R := by
    rw [hRW]
    calc (1 - δ) * ((1 - γ) * B)
        ≤ (1 - δ) * (∑ y ∈ W, b y) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          rw [hWB]
          nlinarith [hdrop]
      _ = ∑ y ∈ W, (1 - δ) * b y := by rw [Finset.mul_sum]
      _ ≤ ∑ y ∈ W, r y := Finset.sum_le_sum hrl
  have hRhigh : R ≤ (1 + δ) * B := by
    rw [hRW]
    calc (∑ y ∈ W, r y)
        ≤ ∑ y ∈ W, (1 + δ) * b y := Finset.sum_le_sum hru
      _ = (1 + δ) * ∑ y ∈ W, b y := by rw [Finset.mul_sum]
      _ ≤ (1 + δ) * B := by
          apply mul_le_mul_of_nonneg_left hWBle (by linarith)
  have hRpos : 0 < R := by nlinarith
  -- split off the dropped part
  have hsplit := Finset.sum_sdiff (f := fun y => |r y / R - b y / B|) hW
  rw [← hsplit]
  have hoff : (∑ y ∈ range n \ W, |r y / R - b y / B|) ≤ γ := by
    have h : ∀ y ∈ range n \ W, |r y / R - b y / B| = b y / B := by
      intro y hy
      rw [Finset.mem_sdiff] at hy
      have hby : 0 ≤ b y / B := div_nonneg (hb y hy.1) (le_of_lt hBpos)
      rw [hr0 y hy.1 hy.2, zero_div, zero_sub, abs_neg, abs_of_nonneg hby]
    rw [Finset.sum_congr rfl h, ← Finset.sum_div, div_le_iff₀ hBpos]
    exact hdrop
  have habs_rb : ∀ y ∈ W, |r y - b y| ≤ δ * b y := by
    intro y hy
    rw [abs_le]
    constructor
    · have h := hrl y hy
      nlinarith [hbW y hy]
    · have h := hru y hy
      nlinarith [hbW y hy]
  have hBR : |B - R| ≤ (δ + γ) * B := by
    rw [abs_le]
    constructor
    · nlinarith [hRhigh, hBpos, hγ0]
    · nlinarith [hRlow, hBpos, mul_nonneg hδ0 hγ0]
  have hon : (∑ y ∈ W, |r y / R - b y / B|) ≤ (2 * δ + γ) * B / R := by
    have hpoint : ∀ y ∈ W, |r y / R - b y / B| ≤
        |r y - b y| / R + b y * |B - R| / (R * B) := by
      intro y hy
      have h2 : |r y / R - b y / R| = |r y - b y| / R := by
        rw [div_sub_div_same, abs_div, abs_of_pos hRpos]
      have h3 : |b y / R - b y / B| = b y * |B - R| / (R * B) := by
        rw [div_sub_div _ _ (ne_of_gt hRpos) (ne_of_gt hBpos), abs_div,
          abs_of_pos (mul_pos hRpos hBpos)]
        congr 1
        rw [show b y * B - R * b y = b y * (B - R) by ring, abs_mul,
          abs_of_nonneg (hbW y hy)]
      calc |r y / R - b y / B|
          ≤ |r y / R - b y / R| + |b y / R - b y / B| := abs_sub_le _ _ _
        _ = |r y - b y| / R + b y * |B - R| / (R * B) := by rw [h2, h3]
    refine le_trans (Finset.sum_le_sum hpoint) ?_
    rw [Finset.sum_add_distrib]
    have hsum_rb : (∑ y ∈ W, |r y - b y|) ≤ δ * B := by
      calc (∑ y ∈ W, |r y - b y|) ≤ ∑ y ∈ W, δ * b y := Finset.sum_le_sum habs_rb
        _ = δ * ∑ y ∈ W, b y := by rw [Finset.mul_sum]
        _ ≤ δ * B := mul_le_mul_of_nonneg_left hWBle hδ0
    have hs1 : (∑ y ∈ W, |r y - b y| / R) ≤ δ * B / R := by
      rw [← Finset.sum_div, div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hsum_rb (le_of_lt (inv_pos.mpr hRpos))
    have hs2 : (∑ y ∈ W, b y * |B - R| / (R * B)) ≤ (δ + γ) * B / R := by
      rw [← Finset.sum_div, ← Finset.sum_mul]
      have h4 : (∑ y ∈ W, b y) * |B - R| ≤ B * ((δ + γ) * B) :=
        mul_le_mul hWBle hBR (abs_nonneg _) (le_of_lt hBpos)
      have hs2a : (∑ y ∈ W, b y) * |B - R| / (R * B) ≤ B * ((δ + γ) * B) / (R * B) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right h4
          (le_of_lt (inv_pos.mpr (mul_pos hRpos hBpos)))
      refine le_trans hs2a (le_of_eq ?_)
      field_simp
    refine le_trans (add_le_add hs1 hs2) (le_of_eq ?_)
    field_simp
    ring
  have hDpos : (0:ℚ) < (1 - δ) * (1 - γ) := by nlinarith
  have hf1 : (0:ℚ) ≤ 2 * δ + γ := by linarith
  have hBRle : (2 * δ + γ) * B / R ≤ (2 * δ + γ) / ((1 - δ) * (1 - γ)) := by
    rw [div_le_div_iff₀ hRpos hDpos]
    nlinarith [mul_le_mul_of_nonneg_left hRlow hf1]
  have hfinal : γ + (2 * δ + γ) / ((1 - δ) * (1 - γ)) ≤ 4 * δ + 3 * γ := by
    have h6 : (2 * δ + γ) / ((1 - δ) * (1 - γ)) ≤ 4 * δ + 2 * γ := by
      rw [div_le_iff₀ hDpos]
      have hf2 : (0:ℚ) ≤ 1 - 2 * δ - 2 * γ + 2 * δ * γ := by
        nlinarith [mul_nonneg hδ0 hγ0]
      nlinarith [mul_nonneg hf1 hf2]
    linarith
  calc (∑ y ∈ range n \ W, |r y / R - b y / B|) + ∑ y ∈ W, |r y / R - b y / B|
      ≤ γ + (2 * δ + γ) * B / R := add_le_add hoff hon
    _ ≤ γ + (2 * δ + γ) / ((1 - δ) * (1 - γ)) := by linarith [hBRle]
    _ ≤ 4 * δ + 3 * γ := hfinal
