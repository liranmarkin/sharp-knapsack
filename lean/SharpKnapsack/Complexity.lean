/-
# Operation-count analysis: the algorithm runs in polynomial time

The paper's Theorem 1 has two halves: the `(1+ε)` approximation guarantee
(verified in `DivideConquer.lean`) and the running-time bound. This file
formalizes the second half in the standard style for verified complexity:
an explicit *cost model* - recursively defined cost functions that mirror
the structure of the algorithm and charge each list operation its length -
and a machine-checked proof that the total cost is bounded by an explicit
polynomial in `n` and `1/ε`. Together with `approxCount_spec` this makes the
formal claim "the algorithm is an FPTAS" complete: correct *and* polynomial.

The bound proven here is deliberately loose (a low-degree polynomial with a
generous constant): with the rational sparsification schedule used in this
development the paper's sharp `O(n^{2.5}...)` exponent is not even statable
in `ℚ`, and looseness buys short proofs. The paper's own tighter analysis
remains pen-and-paper.

This part: the engine of the whole analysis, the *threshold growth* of
sparsification. `sparsify δ` outputs one point per breakpoint, and each
breakpoint bumps the threshold `r ← max (r+1) ⌊(1+δ)r⌋` at least once, so
the output size is at most the total number of bump steps. Each step gains
`max 1 ⌊δr⌋`, so `r` doubles within `⌈2/δ⌉+1` steps, hence exceeds any total
mass `T` within `(⌈2/δ⌉+1)·(log₂ T + 1)` steps - the paper's
`log_{1+δ} M` representation-size bound, in rational form.
-/

import SharpKnapsack.DivideConquer

open SparseFun

/-- Number of threshold-bump steps performed before the threshold exceeds
`target` (the recursion mirrors `bumpR`). -/
def bumpSteps (δ : ℚ) (r target : ℕ) : ℕ :=
  if r ≤ target then bumpSteps δ (nextR δ r) target + 1 else 0
termination_by target + 1 - r
decreasing_by
  have h : r + 1 ≤ nextR δ r := Nat.le_max_left _ _
  omega

theorem bumpSteps_of_gt {δ : ℚ} {r target : ℕ} (h : ¬ r ≤ target) :
    bumpSteps δ r target = 0 := by
  rw [bumpSteps, if_neg h]

/-- One bump step gains exactly `max 1 ⌊δr⌋`. -/
theorem nextR_eq (δ : ℚ) (hδ : 0 ≤ δ) (r : ℕ) :
    nextR δ r = r + max 1 ⌊δ * r⌋₊ := by
  unfold nextR
  have h1 : (1 + δ) * r = δ * r + (r : ℚ) := by ring
  rw [h1, Nat.floor_add_natCast (by positivity)]
  omega

theorem nextR_mono (δ : ℚ) (hδ : 0 ≤ δ) {r₁ r₂ : ℕ} (h : r₁ ≤ r₂) :
    nextR δ r₁ ≤ nextR δ r₂ := by
  rw [nextR_eq δ hδ, nextR_eq δ hδ]
  have hf : ⌊δ * (r₁ : ℚ)⌋₊ ≤ ⌊δ * (r₂ : ℚ)⌋₊ := by
    apply Nat.floor_le_floor
    have : (r₁ : ℚ) ≤ r₂ := by exact_mod_cast h
    nlinarith
  omega

theorem le_nextR (δ : ℚ) (r : ℕ) : r + 1 ≤ nextR δ r :=
  Nat.le_max_left _ _

/-- More bumps are needed from a lower starting threshold. -/
theorem bumpSteps_antitone (δ : ℚ) (hδ : 0 ≤ δ) (target : ℕ) :
    ∀ r₁ r₂, r₁ ≤ r₂ → bumpSteps δ r₂ target ≤ bumpSteps δ r₁ target := by
  intro r₁
  induction r₁ using bumpSteps.induct δ target with
  | case1 r₁ hle ih =>
    intro r₂ h12
    by_cases h2 : r₂ ≤ target
    · rw [show bumpSteps δ r₂ target = bumpSteps δ (nextR δ r₂) target + 1 by
        rw [bumpSteps, if_pos h2]]
      rw [show bumpSteps δ r₁ target = bumpSteps δ (nextR δ r₁) target + 1 by
        rw [bumpSteps, if_pos hle]]
      have := ih (nextR δ r₂) (nextR_mono δ hδ h12)
      omega
    · rw [bumpSteps_of_gt h2]
      omega
  | case2 r₁ hgt =>
    intro r₂ h12
    have h2 : ¬ r₂ ≤ target := by omega
    rw [bumpSteps_of_gt hgt, bumpSteps_of_gt h2]

/-- Chain decomposition: `m` explicit steps can be split off the front. -/
theorem bumpSteps_le_iterate (δ : ℚ) (target : ℕ) (m : ℕ) :
    ∀ r, bumpSteps δ r target ≤ m + bumpSteps δ ((nextR δ)^[m] r) target := by
  induction m with
  | zero => intro r; simp
  | succ m ih =>
    intro r
    by_cases h : r ≤ target
    · rw [bumpSteps, if_pos h]
      have := ih (nextR δ r)
      rw [Function.iterate_succ_apply]
      omega
    · rw [bumpSteps_of_gt h]
      omega

/-- Iterated steps gain at least `m` times the initial gain. -/
theorem iterate_nextR_ge (δ : ℚ) (hδ : 0 ≤ δ) (r : ℕ) :
    ∀ m, r + m * max 1 ⌊δ * r⌋₊ ≤ (nextR δ)^[m] r := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    have hr : r ≤ (nextR δ)^[m] r := le_trans (Nat.le_add_right _ _) ih
    rw [nextR_eq δ hδ]
    have hf : ⌊δ * (r : ℚ)⌋₊ ≤ ⌊δ * ((nextR δ)^[m] r : ℚ)⌋₊ := by
      apply Nat.floor_le_floor
      have : (r : ℚ) ≤ ((nextR δ)^[m] r : ℚ) := by exact_mod_cast hr
      nlinarith
    rw [Nat.succ_mul]
    omega

/-- The number of steps needed to double the threshold. -/
def doubleSteps (δ : ℚ) : ℕ := ⌈2 / δ⌉₊ + 1

/-- Within `doubleSteps δ` bump steps the threshold at least doubles. -/
theorem iterate_nextR_double (δ : ℚ) (hδ : 0 < δ) {r : ℕ} (hr : 1 ≤ r) :
    2 * r ≤ (nextR δ)^[doubleSteps δ] r := by
  refine le_trans ?_ (iterate_nextR_ge δ (le_of_lt hδ) r (doubleSteps δ))
  -- Enough: r ≤ doubleSteps δ * max 1 ⌊δr⌋.
  have key : r ≤ doubleSteps δ * max 1 ⌊δ * (r : ℚ)⌋₊ := by
    by_cases hcase : (r : ℚ) ≤ 2 / δ
    · -- Small r: the +1 gains alone suffice, since r ≤ ⌈2/δ⌉.
      have h1 : r ≤ ⌈2 / δ⌉₊ := by
        have := Nat.le_ceil (2 / δ)
        exact_mod_cast Nat.cast_le.mp (le_trans hcase (Nat.le_ceil _))
      calc r ≤ ⌈2 / δ⌉₊ + 1 := by omega
        _ = doubleSteps δ * 1 := by unfold doubleSteps; omega
        _ ≤ doubleSteps δ * max 1 ⌊δ * (r : ℚ)⌋₊ :=
            Nat.mul_le_mul_left _ (Nat.le_max_left _ _)
    · -- Large r: δr > 2, so ⌊δr⌋ > δr/2, and ⌈2/δ⌉ ≥ 2/δ steps of that size
      -- cover r.
      rw [not_le] at hcase
      have h2 : (2 : ℚ) < δ * r := by
        rw [div_lt_iff₀ hδ] at hcase
        linarith
      have hfloor : δ * (r : ℚ) / 2 < (⌊δ * (r : ℚ)⌋₊ : ℚ) := by
        have hlt := Nat.lt_floor_add_one (δ * (r : ℚ))
        have hge : (⌊δ * (r : ℚ)⌋₊ : ℚ) > δ * r - 1 := by linarith
        linarith
      have hceil : (2 : ℚ) / δ ≤ (⌈2 / δ⌉₊ : ℚ) := Nat.le_ceil _
      have hpos : (0 : ℚ) < (⌊δ * (r : ℚ)⌋₊ : ℚ) := by linarith
      have hmul : (r : ℚ) ≤ (⌈2 / δ⌉₊ : ℚ) * ⌊δ * (r : ℚ)⌋₊ := by
        have step1 : (2 / δ) * (δ * r / 2) = (r : ℚ) := by
          field_simp
        calc (r : ℚ) = (2 / δ) * (δ * r / 2) := step1.symm
          _ ≤ (⌈2 / δ⌉₊ : ℚ) * (δ * r / 2) := by
              apply mul_le_mul_of_nonneg_right hceil
              linarith
          _ ≤ (⌈2 / δ⌉₊ : ℚ) * ⌊δ * (r : ℚ)⌋₊ := by
              apply mul_le_mul_of_nonneg_left (le_of_lt hfloor)
              positivity
      have hnat : r ≤ ⌈2 / δ⌉₊ * ⌊δ * (r : ℚ)⌋₊ := by exact_mod_cast hmul
      calc r ≤ ⌈2 / δ⌉₊ * ⌊δ * (r : ℚ)⌋₊ := hnat
        _ ≤ doubleSteps δ * ⌊δ * (r : ℚ)⌋₊ := by
            unfold doubleSteps
            exact Nat.mul_le_mul_right _ (by omega)
        _ ≤ doubleSteps δ * max 1 ⌊δ * (r : ℚ)⌋₊ :=
            Nat.mul_le_mul_left _ (Nat.le_max_right _ _)
  omega

/-- If `target < 2^k · r` then at most `doubleSteps δ · k` bumps happen:
each block of `doubleSteps δ` steps doubles the threshold. -/
theorem bumpSteps_le_of_pow (δ : ℚ) (hδ : 0 < δ) (target : ℕ) :
    ∀ k r, 1 ≤ r → target < 2 ^ k * r →
    bumpSteps δ r target ≤ doubleSteps δ * k := by
  intro k
  induction k with
  | zero =>
    intro r hr hlt
    simp at hlt
    rw [bumpSteps_of_gt (by omega)]
    omega
  | succ k ih =>
    intro r hr hlt
    by_cases h : r ≤ target
    · calc bumpSteps δ r target
          ≤ doubleSteps δ + bumpSteps δ ((nextR δ)^[doubleSteps δ] r) target :=
            bumpSteps_le_iterate δ target (doubleSteps δ) r
        _ ≤ doubleSteps δ + bumpSteps δ (2 * r) target := by
            have hd := iterate_nextR_double δ hδ hr
            have := bumpSteps_antitone δ (le_of_lt hδ) target (2 * r) _ hd
            omega
        _ ≤ doubleSteps δ + doubleSteps δ * k := by
            have hlt' : target < 2 ^ k * (2 * r) := by
              rw [pow_succ] at hlt
              have : 2 ^ (k) * 2 * r = 2 ^ k * (2 * r) := by ring
              omega
            have := ih (2 * r) (by omega) hlt'
            omega
        _ = doubleSteps δ * (k + 1) := by ring
    · rw [bumpSteps_of_gt h]
      omega

/-- **Threshold-growth bound**: starting from threshold 1, at most
`(⌈2/δ⌉+1)·(log₂ target + 1)` bump steps happen before the threshold
exceeds `target`. This is the paper's `log_{1+δ}` size bound. -/
theorem bumpSteps_le (δ : ℚ) (hδ : 0 < δ) (target : ℕ) :
    bumpSteps δ 1 target ≤ doubleSteps δ * (Nat.log 2 target + 1) := by
  refine bumpSteps_le_of_pow δ hδ target (Nat.log 2 target + 1) 1 le_rfl ?_
  have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) target
  omega

/-! ## Output size and mass of sparsification

Every point emitted by the scan corresponds to a breakpoint, and every
breakpoint performs at least one threshold bump, so the output length is
bounded by the total number of bump steps - which the previous section
bounded logarithmically. Total mass (the sum of all values) is what the
thresholds chase, and it is preserved or shrunk by every operation.
-/

namespace SparseFun

/-- Total mass of a representation: the sum of its values. For the counting
functions in this development the mass is at most `2^n`, which is what makes
the representation sizes logarithmic. -/
def massOf (L : SparseFun) : ℕ := (L.map (·.2)).sum

theorem massOf_nil : massOf [] = 0 := rfl

theorem massOf_cons (a v : ℕ) (L : SparseFun) :
    massOf ((a, v) :: L) = v + massOf L := by
  simp [massOf]

theorem massOf_append (L M : SparseFun) :
    massOf (L ++ M) = massOf L + massOf M := by
  simp [massOf]

/-- Consuming the bump chain up to an intermediate target `t ≤ T` costs at
least one step of the chain toward `T`. -/
theorem bumpSteps_bumpR (δ : ℚ) (T : ℕ) :
    ∀ t r, r ≤ t → t ≤ T →
    1 + bumpSteps δ (bumpR δ r t) T ≤ bumpSteps δ r T := by
  intro t r
  induction r using bumpR.induct δ t with
  | case1 r hle ih =>
    intro _ hT
    rw [show bumpR δ r t = bumpR δ (nextR δ r) t by rw [bumpR, if_pos hle]]
    rw [show bumpSteps δ r T = bumpSteps δ (nextR δ r) T + 1 by
      rw [bumpSteps, if_pos (by omega)]]
    by_cases h2 : nextR δ r ≤ t
    · have := ih h2 hT
      omega
    · rw [show bumpR δ (nextR δ r) t = nextR δ r by rw [bumpR, if_neg h2]]
      omega
  | case2 r hgt =>
    intro h _
    omega

/-- The scan emits at most one point per bump step (plus the pending one). -/
theorem sparsifyGo_length (δ : ℚ) :
    ∀ (rest : List (ℕ × ℕ)) (acc r : ℕ) (pending : Option (ℕ × ℕ)),
    (sparsifyGo δ rest acc r pending).length
      ≤ (if pending.isSome then 1 else 0) + bumpSteps δ r (acc + massOf rest) := by
  intro rest
  induction rest with
  | nil =>
    intro acc r pending
    match pending with
    | none => simp [sparsifyGo]
    | some (q, base) => simp [sparsifyGo]
  | cons pv rest' ih =>
    intro acc r pending
    obtain ⟨p, v⟩ := pv
    have hmass : acc + massOf ((p, v) :: rest') = (acc + v) + massOf rest' := by
      rw [massOf_cons]; omega
    by_cases hbr : acc + v < r
    · rw [sparsifyGo_cons_lt hbr, hmass]
      exact ih (acc + v) r pending
    · have hle : r ≤ acc + v := by omega
      have hT : acc + v ≤ (acc + v) + massOf rest' := by omega
      have hchain := bumpSteps_bumpR δ ((acc + v) + massOf rest') (acc + v) r hle hT
      match pending with
      | none =>
        rw [sparsifyGo_cons_ge_none hbr, hmass]
        have hrec := ih (acc + v) (bumpR δ r (acc + v)) (some (p, acc))
        simp only [Option.isSome_some, Option.isSome_none, ite_true, ite_false,
          Bool.false_eq_true] at hrec ⊢
        omega
      | some (q, base) =>
        rw [sparsifyGo_cons_ge_some hbr, hmass]
        have hrec := ih (acc + v) (bumpR δ r (acc + v)) (some (p, acc))
        simp only [Option.isSome_some, ite_true, List.length_cons] at hrec ⊢
        omega

/-- **Representation-size bound for sparsification** (the paper's
`|F| ≤ log_{1+δ} M`): the output has at most
`(⌈2/δ⌉+1)·(log₂ mass + 1)` points. -/
theorem sparsify_length (δ : ℚ) (hδ : 0 < δ) (L : SparseFun) :
    (sparsify δ L).length ≤ doubleSteps δ * (Nat.log 2 (massOf L) + 1) := by
  have h := sparsifyGo_length δ L 0 1 none
  simp only [Option.isSome_none, Nat.zero_add] at h
  calc (sparsify δ L).length ≤ bumpSteps δ 1 (massOf L) := by
        unfold sparsify
        simpa using h
    _ ≤ doubleSteps δ * (Nat.log 2 (massOf L) + 1) := bumpSteps_le δ hδ (massOf L)

/-! ### Mass through each operation -/

theorem massOf_shift (w : ℕ) (L : SparseFun) : massOf (shift w L) = massOf L := by
  simp [massOf, shift, List.map_map, Function.comp_def]

theorem massOf_mergeDups (L : SparseFun) : massOf (mergeDups L) = massOf L := by
  induction L using mergeDups.induct with
  | case1 => simp [mergeDups]
  | case2 p => simp [mergeDups]
  | case3 v y w L ih =>
    rw [mergeDups, if_pos rfl, ih, massOf_cons, massOf_cons, massOf_cons]
    omega
  | case4 x v y w L hne ih =>
    rw [mergeDups, if_neg hne, massOf_cons, ih]
    simp [massOf_cons]

theorem massOf_perm {L M : SparseFun} (h : L.Perm M) : massOf L = massOf M :=
  List.Perm.sum_eq (h.map _)

theorem massOf_normalize (L : SparseFun) : massOf (normalize L) = massOf L := by
  unfold normalize
  rw [massOf_mergeDups]
  exact massOf_perm (List.mergeSort_perm L _)

theorem massOf_add (L M : SparseFun) :
    massOf (add L M) = massOf L + massOf M := by
  rw [add, massOf_normalize, massOf_append]

theorem massOf_map_mul (a b : ℕ) (M : SparseFun) :
    massOf (M.map fun q => (a + q.1, b * q.2)) = b * massOf M := by
  induction M with
  | nil => simp [massOf]
  | cons q M ih =>
    rw [List.map_cons, massOf_cons, ih, massOf_cons]
    ring

theorem massOf_conv (L M : SparseFun) :
    massOf (conv L M) = massOf L * massOf M := by
  rw [conv, massOf_normalize]
  induction L with
  | nil => simp [massOf]
  | cons p L ih =>
    rw [List.flatMap_cons, massOf_append, ih, massOf_cons, massOf_map_mul]
    ring

/-- The scan never creates mass: with a pending point whose base is below
`acc`, the emitted mass stays within the remaining input mass. -/
theorem massOf_sparsifyGo_some (δ : ℚ) :
    ∀ (rest : List (ℕ × ℕ)) (acc r q base : ℕ), base ≤ acc →
    base + massOf (sparsifyGo δ rest acc r (some (q, base))) ≤ acc + massOf rest := by
  intro rest
  induction rest with
  | nil =>
    intro acc r q base hb
    rw [sparsifyGo_nil_some, massOf_cons, massOf_nil]
    omega
  | cons pv rest' ih =>
    intro acc r q base hb
    obtain ⟨p, v⟩ := pv
    rw [massOf_cons]
    by_cases hbr : acc + v < r
    · rw [sparsifyGo_cons_lt hbr]
      have := ih (acc + v) r q base (by omega)
      omega
    · rw [sparsifyGo_cons_ge_some hbr, massOf_cons]
      have := ih (acc + v) (bumpR δ r (acc + v)) p acc (by omega)
      omega

theorem massOf_sparsify_le (δ : ℚ) (L : SparseFun) :
    massOf (sparsify δ L) ≤ massOf L := by
  unfold sparsify
  induction L with
  | nil => simp [sparsifyGo, massOf]
  | cons pv rest ih =>
    obtain ⟨p, v⟩ := pv
    rw [massOf_cons]
    by_cases hbr : 0 + v < 1
    · have hv : v = 0 := by omega
      subst hv
      rw [sparsifyGo_cons_lt hbr]
      have hrec := ih
      simp only [Nat.add_zero] at hrec ⊢
      omega
    · rw [sparsifyGo_cons_ge_none hbr]
      have := massOf_sparsifyGo_some δ rest (0 + v) (bumpR δ 1 (0 + v)) p 0 (by omega)
      omega

/-! ### Mass through the algorithms: at most `2^(number of items)` -/

theorem massOf_emptyRep : massOf emptyRep = 1 := rfl

theorem massOf_halmanGo (δ : ℚ) (S : List ℕ) :
    massOf (halmanGo δ S) ≤ 2 ^ S.length := by
  induction S with
  | nil => simp [halmanGo, massOf_emptyRep]
  | cons w S ih =>
    show massOf (insertItem δ (halmanGo δ S) w) ≤ 2 ^ (w :: S).length
    unfold insertItem
    calc massOf (sparsify δ (add (halmanGo δ S) (shift w (halmanGo δ S))))
        ≤ massOf (add (halmanGo δ S) (shift w (halmanGo δ S))) :=
          massOf_sparsify_le _ _
      _ = massOf (halmanGo δ S) + massOf (halmanGo δ S) := by
          rw [massOf_add, massOf_shift]
      _ ≤ 2 ^ S.length + 2 ^ S.length := by omega
      _ = 2 ^ (w :: S).length := by
          rw [List.length_cons, pow_succ]
          ring

theorem massOf_halman (S : List ℕ) (t : ℚ) :
    massOf (halman S t) ≤ 2 ^ S.length := massOf_halmanGo _ S

theorem massOf_dcGo (ε : ℚ) (T : ℕ) (S : List ℕ) (d : ℕ) :
    massOf (dcGo ε T S d) ≤ 2 ^ S.length := by
  rw [dcGo.eq_def]
  by_cases hlen : S.length ≤ max 1 T
  · rw [if_pos hlen]
    exact massOf_halman S _
  · rw [if_neg hlen]
    have hA := massOf_dcGo ε T (S.take (S.length / 2)) (d + 1)
    have hB := massOf_dcGo ε T (S.drop (S.length / 2)) (d + 1)
    calc massOf (sparsify (deltaAt ε d) _)
        ≤ massOf (conv (dcGo ε T (S.take (S.length / 2)) (d + 1))
            (dcGo ε T (S.drop (S.length / 2)) (d + 1))) := massOf_sparsify_le _ _
      _ = massOf (dcGo ε T (S.take (S.length / 2)) (d + 1))
            * massOf (dcGo ε T (S.drop (S.length / 2)) (d + 1)) := massOf_conv _ _
      _ ≤ 2 ^ (S.take (S.length / 2)).length * 2 ^ (S.drop (S.length / 2)).length :=
          Nat.mul_le_mul hA hB
      _ = 2 ^ S.length := by
          rw [← pow_add, List.length_take, List.length_drop]
          congr 1
          omega
termination_by S.length
decreasing_by
  · simp only [List.length_take]
    omega
  · simp only [List.length_drop]
    omega

end SparseFun
