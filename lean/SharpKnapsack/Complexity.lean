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

/-! ## Uniform bound on representation sizes

`⌈1/ε⌉` plays the role of `1/ε` in `ℕ`. On the recursion tree of `dcGo`,
node sizes satisfy `(|S|-1)·2^d ≤ n+1` and `2^d ≤ 2(n+1)` (sizes at least
halve while depth increments), which turns every depth-dependent quantity
into a polynomial in `n` alone. The result: *every* representation the
algorithm ever constructs has at most `2431·⌈1/ε⌉·(n+1)³` points.
-/

namespace SparseFun

theorem one_le_invE {ε : ℚ} (hε0 : 0 < ε) : 1 ≤ ⌈1 / ε⌉₊ := by
  have h : (0 : ℚ) < 1 / ε := by positivity
  exact Nat.ceil_pos.mpr h

theorem two_div_deltaAt {ε : ℚ} (hε0 : 0 < ε) (d : ℕ) :
    (2 : ℚ) / deltaAt ε d ≤ 40 * ⌈1 / ε⌉₊ * 4 ^ d := by
  have hpow : (0 : ℚ) < ((2 : ℚ) / 5) ^ d := by positivity
  have heq : (2 : ℚ) / deltaAt ε d = 40 / ε * (5 / 2) ^ d := by
    unfold deltaAt
    rw [show ((5 : ℚ) / 2) ^ d = (((2 : ℚ) / 5) ^ d)⁻¹ by
      rw [← inv_pow]; norm_num]
    field_simp
    norm_num
  rw [heq]
  have h1 : (1 : ℚ) / ε ≤ (⌈1 / ε⌉₊ : ℚ) := Nat.le_ceil _
  have h2 : ((5 : ℚ) / 2) ^ d ≤ (4 : ℚ) ^ d := by
    gcongr
    norm_num
  have h3 : (40 : ℚ) / ε = 40 * (1 / ε) := by ring
  rw [h3]
  have h4 : (0 : ℚ) < 1 / ε := by positivity
  calc (40 : ℚ) * (1 / ε) * (5 / 2) ^ d
      ≤ 40 * (⌈1 / ε⌉₊ : ℚ) * (5 / 2) ^ d := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        nlinarith
    _ ≤ 40 * (⌈1 / ε⌉₊ : ℚ) * 4 ^ d := by
        apply mul_le_mul_of_nonneg_left h2
        positivity

theorem doubleSteps_deltaAt {ε : ℚ} (hε0 : 0 < ε) (d : ℕ) :
    doubleSteps (deltaAt ε d) ≤ 41 * ⌈1 / ε⌉₊ * 4 ^ d := by
  have h := two_div_deltaAt hε0 d
  have hceil : ⌈(2 : ℚ) / deltaAt ε d⌉₊ ≤ 40 * ⌈1 / ε⌉₊ * 4 ^ d := by
    rw [Nat.ceil_le]
    calc (2 : ℚ) / deltaAt ε d ≤ 40 * ⌈1 / ε⌉₊ * 4 ^ d := h
      _ = ((40 * ⌈1 / ε⌉₊ * 4 ^ d : ℕ) : ℚ) := by push_cast; ring
  have hE : 1 ≤ ⌈1 / ε⌉₊ := one_le_invE hε0
  have h4 : 1 ≤ 4 ^ d := Nat.one_le_pow _ _ (by omega)
  have hmul : 1 ≤ ⌈1 / ε⌉₊ * 4 ^ d := le_trans hE (Nat.le_mul_of_pos_right _ (by omega))
  calc doubleSteps (deltaAt ε d) = ⌈(2 : ℚ) / deltaAt ε d⌉₊ + 1 := rfl
    _ ≤ 40 * ⌈1 / ε⌉₊ * 4 ^ d + 1 := by omega
    _ ≤ 41 * ⌈1 / ε⌉₊ * 4 ^ d := by nlinarith

/-- Bound for the per-item parameter used by `halman S (deltaAt ε d)`. -/
theorem doubleSteps_halman_delta {ε : ℚ} (hε0 : 0 < ε) (d : ℕ) {s : ℕ} (hs : 1 ≤ s) :
    doubleSteps (deltaAt ε d / (2 * s)) ≤ 81 * s * ⌈1 / ε⌉₊ * 4 ^ d := by
  have hδ : (0 : ℚ) < deltaAt ε d := deltaAt_pos hε0 d
  have hs' : (0 : ℚ) < (s : ℚ) := by exact_mod_cast hs
  have heq : (2 : ℚ) / (deltaAt ε d / (2 * s)) = (2 * s) * (2 / deltaAt ε d) := by
    field_simp
  have h := two_div_deltaAt hε0 d
  have hceil : ⌈(2 : ℚ) / (deltaAt ε d / (2 * s))⌉₊ ≤ 80 * s * ⌈1 / ε⌉₊ * 4 ^ d := by
    rw [Nat.ceil_le, heq]
    calc (2 * (s : ℚ)) * (2 / deltaAt ε d)
        ≤ (2 * s) * (40 * ⌈1 / ε⌉₊ * 4 ^ d) := by
          apply mul_le_mul_of_nonneg_left h
          positivity
      _ = ((80 * s * ⌈1 / ε⌉₊ * 4 ^ d : ℕ) : ℚ) := by push_cast; ring
  have hE : 1 ≤ ⌈1 / ε⌉₊ := one_le_invE hε0
  have h4 : 1 ≤ 4 ^ d := Nat.one_le_pow _ _ (by omega)
  have hpos : 1 ≤ s * ⌈1 / ε⌉₊ * 4 ^ d := by
    have := Nat.mul_le_mul (Nat.mul_le_mul hs hE) h4
    omega
  calc doubleSteps (deltaAt ε d / (2 * s)) = ⌈(2 : ℚ) / (deltaAt ε d / (2 * s))⌉₊ + 1 := rfl
    _ ≤ 80 * s * ⌈1 / ε⌉₊ * 4 ^ d + 1 := by omega
    _ ≤ 81 * s * ⌈1 / ε⌉₊ * 4 ^ d := by nlinarith

/-- Every intermediate representation of the insertion loop has at most
`1 + doubleSteps δ · (n+2)` points, where `n` is the number of items. -/
theorem halmanGo_length (δ : ℚ) (hδ : 0 < δ) (S : List ℕ) :
    (halmanGo δ S).length ≤ 1 + doubleSteps δ * (S.length + 2) := by
  induction S with
  | nil => simp [halmanGo, emptyRep]
  | cons w S ih =>
    show (insertItem δ (halmanGo δ S) w).length ≤ _
    unfold insertItem
    set K := halmanGo δ S with hK
    have hmass : massOf (add K (shift w K)) ≤ 2 ^ (S.length + 1) := by
      rw [massOf_add, massOf_shift]
      have hm := massOf_halmanGo δ S
      rw [← hK] at hm
      rw [pow_succ]
      omega
    have hlog : Nat.log 2 (massOf (add K (shift w K))) ≤ S.length + 1 := by
      calc Nat.log 2 (massOf (add K (shift w K)))
          ≤ Nat.log 2 (2 ^ (S.length + 1)) := Nat.log_mono_right hmass
        _ = S.length + 1 := Nat.log_pow (b := 2) (by norm_num) _
    calc (sparsify δ (add K (shift w K))).length
        ≤ doubleSteps δ * (Nat.log 2 (massOf (add K (shift w K))) + 1) :=
          sparsify_length δ hδ _
      _ ≤ doubleSteps δ * ((S.length + 1) + 1) := by
          apply Nat.mul_le_mul_left
          omega
      _ ≤ 1 + doubleSteps δ * ((w :: S).length + 2) := by
          have h1 : (S.length + 1) + 1 ≤ (w :: S).length + 2 := by simp
          have := Nat.mul_le_mul_left (doubleSteps δ) h1
          omega

/-- The uniform representation bound: `2431·⌈1/ε⌉·(n+1)³`. -/
def repBound (ε : ℚ) (n : ℕ) : ℕ := 2431 * ⌈1 / ε⌉₊ * (n + 1) ^ 3

/-- **Every representation produced by a node of the recursion tree has at
most `repBound ε n` points.** The hypotheses `(|S|-1)·2^d ≤ n+1` and
`2^d ≤ 2(n+1)` are the tree invariants: they hold at the root `(S, 0)` with
`n = |S|` and are preserved when a node splits its list and increments `d`. -/
theorem dcGo_length {ε : ℚ} (hε0 : 0 < ε) (n : ℕ) (T : ℕ) (S : List ℕ) (d : ℕ)
    (hd : 2 ^ d ≤ 2 * (n + 1)) (hs : (S.length - 1) * 2 ^ d ≤ n + 1) :
    (dcGo ε T S d).length ≤ repBound ε n := by
  have hE : 1 ≤ ⌈1 / ε⌉₊ := one_le_invE hε0
  have h4d : (4 : ℕ) ^ d = 2 ^ d * 2 ^ d := by
    rw [← Nat.mul_pow]
  have hs2d : S.length * 2 ^ d ≤ 3 * (n + 1) := by
    have h1 : 1 ≤ 2 ^ d := Nat.one_le_two_pow
    have hsub : (S.length - 1) * 2 ^ d = S.length * 2 ^ d - 1 * 2 ^ d :=
      Nat.sub_mul _ _ _
    rw [hsub] at hs
    omega
  rw [dcGo.eq_def]
  by_cases hlen : S.length ≤ max 1 T
  · -- Bottom node: a halman output.
    rw [if_pos hlen]
    unfold halman
    rcases Nat.eq_zero_or_pos S.length with h0 | hpos
    · have hnil : S = [] := List.length_eq_zero_iff.mp h0
      subst hnil
      show (halmanGo _ []).length ≤ _
      unfold halmanGo emptyRep repBound
      have h3 : 1 ≤ (n + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
      simp only [List.length_cons, List.length_nil]
      nlinarith
    · have hδ' : (0 : ℚ) < deltaAt ε d / (2 * S.length) := by
        have h1 : (0 : ℚ) < deltaAt ε d := deltaAt_pos hε0 d
        have h2 : (0 : ℚ) < (S.length : ℚ) := by exact_mod_cast hpos
        positivity
      have hlen' := halmanGo_length _ hδ' S
      have hds := doubleSteps_halman_delta hε0 d hpos
      -- Assemble: 1 + 81·s·E·4^d·(s+2) ≤ 2431·E·(n+1)³.
      have hs3 : S.length ≤ 3 * (n + 1) := by
        have h1 : 1 ≤ 2 ^ d := Nat.one_le_two_pow
        have h2 : S.length * 1 ≤ S.length * 2 ^ d := Nat.mul_le_mul_left _ h1
        omega
      have hstep : doubleSteps (deltaAt ε d / (2 * S.length)) * (S.length + 2)
          ≤ 81 * S.length * ⌈1 / ε⌉₊ * 4 ^ d * (S.length + 2) :=
        Nat.mul_le_mul_right _ hds
      have hkey : 81 * S.length * ⌈1 / ε⌉₊ * 4 ^ d * (S.length + 2)
          ≤ 2430 * ⌈1 / ε⌉₊ * (n + 1) ^ 3 := by
        -- s·4^d = (s·2^d)·2^d ≤ 3(n+1)·2(n+1), and s+2 ≤ 3(n+1)+2 ≤ 5(n+1).
        have e1 : 81 * S.length * ⌈1 / ε⌉₊ * 4 ^ d * (S.length + 2)
            = 81 * ⌈1 / ε⌉₊ * ((S.length * 2 ^ d) * 2 ^ d * (S.length + 2)) := by
          rw [h4d]; ring
        have e2 : (S.length * 2 ^ d) * 2 ^ d * (S.length + 2)
            ≤ (3 * (n + 1)) * (2 * (n + 1)) * (5 * (n + 1)) := by
          have h5 : S.length + 2 ≤ 5 * (n + 1) := by omega
          exact Nat.mul_le_mul (Nat.mul_le_mul hs2d hd) h5
        have e3 : (3 * (n + 1)) * (2 * (n + 1)) * (5 * (n + 1)) = 30 * (n + 1) ^ 3 := by
          ring
        calc 81 * S.length * ⌈1 / ε⌉₊ * 4 ^ d * (S.length + 2)
            = 81 * ⌈1 / ε⌉₊ * ((S.length * 2 ^ d) * 2 ^ d * (S.length + 2)) := e1
          _ ≤ 81 * ⌈1 / ε⌉₊ * (30 * (n + 1) ^ 3) := by
              apply Nat.mul_le_mul_left
              rw [← e3]; exact e2
          _ = 2430 * ⌈1 / ε⌉₊ * (n + 1) ^ 3 := by ring
      unfold repBound
      have hone : 1 ≤ ⌈1 / ε⌉₊ * (n + 1) ^ 3 := by
        have : 1 ≤ (n + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
        nlinarith
      calc (halmanGo (deltaAt ε d / (2 * S.length)) S).length
          ≤ 1 + doubleSteps (deltaAt ε d / (2 * S.length)) * (S.length + 2) := hlen'
        _ ≤ 1 + 2430 * ⌈1 / ε⌉₊ * (n + 1) ^ 3 := by
            have := le_trans hstep hkey
            omega
        _ ≤ 2431 * ⌈1 / ε⌉₊ * (n + 1) ^ 3 := by nlinarith
  · -- Internal node: a sparsify output whose input mass is at most 2^|S|.
    rw [if_neg hlen]
    have hδd : (0 : ℚ) < deltaAt ε d := deltaAt_pos hε0 d
    set A := dcGo ε T (S.take (S.length / 2)) (d + 1)
    set B := dcGo ε T (S.drop (S.length / 2)) (d + 1)
    have hmass : massOf (conv A B) ≤ 2 ^ S.length := by
      rw [massOf_conv]
      calc massOf A * massOf B
          ≤ 2 ^ (S.take (S.length / 2)).length * 2 ^ (S.drop (S.length / 2)).length :=
            Nat.mul_le_mul (massOf_dcGo ε T _ _) (massOf_dcGo ε T _ _)
        _ = 2 ^ S.length := by
            rw [← pow_add, List.length_take, List.length_drop]
            congr 1
            omega
    have hlog : Nat.log 2 (massOf (conv A B)) ≤ S.length := by
      calc Nat.log 2 (massOf (conv A B)) ≤ Nat.log 2 (2 ^ S.length) :=
            Nat.log_mono_right hmass
        _ = S.length := Nat.log_pow (b := 2) (by norm_num) _
    have hds := doubleSteps_deltaAt hε0 d
    calc (sparsify (deltaAt ε d) (conv A B)).length
        ≤ doubleSteps (deltaAt ε d) * (Nat.log 2 (massOf (conv A B)) + 1) :=
          sparsify_length _ hδd _
      _ ≤ (41 * ⌈1 / ε⌉₊ * 4 ^ d) * (S.length + 1) := by
          exact Nat.mul_le_mul hds (by omega)
      _ ≤ repBound ε n := by
          unfold repBound
          have e1 : 41 * ⌈1 / ε⌉₊ * 4 ^ d * (S.length + 1)
              ≤ 41 * ⌈1 / ε⌉₊ * (2 ^ d * 2 ^ d * (2 * S.length)) := by
            have : S.length + 1 ≤ 2 * S.length := by omega
            calc 41 * ⌈1 / ε⌉₊ * 4 ^ d * (S.length + 1)
                ≤ 41 * ⌈1 / ε⌉₊ * 4 ^ d * (2 * S.length) :=
                  Nat.mul_le_mul_left _ this
              _ = 41 * ⌈1 / ε⌉₊ * (2 ^ d * 2 ^ d * (2 * S.length)) := by
                  rw [h4d]; ring
          have e2 : 2 ^ d * 2 ^ d * (2 * S.length) ≤ 2 * (n + 1) * (2 * (3 * (n + 1))) := by
            have := Nat.mul_le_mul hd (Nat.mul_le_mul_left 2 hs2d)
            calc 2 ^ d * 2 ^ d * (2 * S.length) = 2 ^ d * (2 * (S.length * 2 ^ d)) := by
                  ring
              _ ≤ 2 * (n + 1) * (2 * (3 * (n + 1))) :=
                  Nat.mul_le_mul hd (Nat.mul_le_mul_left 2 hs2d)
          have e3 : 2 * (n + 1) * (2 * (3 * (n + 1))) = 12 * (n + 1) ^ 2 := by ring
          have e4 : 41 * ⌈1 / ε⌉₊ * (12 * (n + 1) ^ 2) ≤ 2431 * ⌈1 / ε⌉₊ * (n + 1) ^ 3 := by
            have : (n + 1) ^ 2 ≤ (n + 1) ^ 3 :=
              Nat.pow_le_pow_right (by omega) (by omega)
            nlinarith
          calc 41 * ⌈1 / ε⌉₊ * 4 ^ d * (S.length + 1)
              ≤ 41 * ⌈1 / ε⌉₊ * (2 ^ d * 2 ^ d * (2 * S.length)) := e1
            _ ≤ 41 * ⌈1 / ε⌉₊ * (12 * (n + 1) ^ 2) := by
                apply Nat.mul_le_mul_left
                rw [← e3]; exact e2
            _ ≤ 2431 * ⌈1 / ε⌉₊ * (n + 1) ^ 3 := e4

end SparseFun

/-! ## The cost model

Each operation is charged a cost mirroring its obvious list-level operation
count: linear scans cost the list length, sorting `k` elements costs
`(k+1)·(log₂(k+1)+2)` (mergeSort-style), a convolution generates
`|L|·|M|` pairs and sorts them, and a sparsification pays for its scan plus
its threshold bumps. The cost functions recurse exactly as the algorithms do,
so a bound on them is a bound on the number of elementary operations the
algorithms perform.
-/

namespace SparseFun

def sortCost (k : ℕ) : ℕ := (k + 1) * (Nat.log 2 (k + 1) + 2)

def addCost (L M : SparseFun) : ℕ :=
  sortCost (L.length + M.length) + (L.length + M.length) + 1

def convCost (L M : SparseFun) : ℕ :=
  sortCost (L.length * M.length) + L.length * M.length + 1

def sparsifyCost (δ : ℚ) (L : SparseFun) : ℕ :=
  L.length + bumpSteps δ 1 (massOf L) + 1

def queryCost (L : SparseFun) : ℕ := L.length + 1

def insertItemCost (δ : ℚ) (K : SparseFun) (w : ℕ) : ℕ :=
  (K.length + 1) + addCost K (shift w K) + sparsifyCost δ (add K (shift w K))

def halmanGoCost (δ : ℚ) : List ℕ → ℕ
  | [] => 1
  | w :: S => halmanGoCost δ S + insertItemCost δ (halmanGo δ S) w

def halmanCost (S : List ℕ) (t : ℚ) : ℕ := halmanGoCost (t / (2 * S.length)) S

def dcGoCost (ε : ℚ) (T : ℕ) (S : List ℕ) (d : ℕ) : ℕ :=
  if S.length ≤ max 1 T then
    halmanCost S (deltaAt ε d)
  else
    dcGoCost ε T (S.take (S.length / 2)) (d + 1) +
    dcGoCost ε T (S.drop (S.length / 2)) (d + 1) +
    convCost (dcGo ε T (S.take (S.length / 2)) (d + 1))
             (dcGo ε T (S.drop (S.length / 2)) (d + 1)) +
    sparsifyCost (deltaAt ε d)
      (conv (dcGo ε T (S.take (S.length / 2)) (d + 1))
            (dcGo ε T (S.drop (S.length / 2)) (d + 1)))
termination_by S.length
decreasing_by
  · simp only [List.length_take]
    omega
  · simp only [List.length_drop]
    omega

/-- Total cost of answering a #Knapsack instance. -/
def approxCountCost (S : List ℕ) (_C : ℕ) (ε : ℚ) : ℕ :=
  dcGoCost ε (Nat.sqrt S.length) S 0 + queryCost (dc S ε)

/-! ### Length bounds for the executable operations -/

theorem mergeDups_length_le (L : SparseFun) : (mergeDups L).length ≤ L.length := by
  induction L using mergeDups.induct with
  | case1 => simp [mergeDups]
  | case2 p => simp [mergeDups]
  | case3 v y w L ih =>
    rw [mergeDups, if_pos rfl]
    simp only [List.length_cons] at ih ⊢
    omega
  | case4 x v y w L hne ih =>
    rw [mergeDups, if_neg hne]
    simp only [List.length_cons] at ih ⊢
    omega

theorem normalize_length_le (L : SparseFun) : (normalize L).length ≤ L.length := by
  unfold normalize
  calc (mergeDups (L.mergeSort _)).length ≤ (L.mergeSort _).length :=
        mergeDups_length_le _
    _ = L.length := (List.mergeSort_perm L _).length_eq

theorem shift_length (w : ℕ) (L : SparseFun) : (shift w L).length = L.length := by
  simp [shift]

theorem add_length_le (L M : SparseFun) :
    (add L M).length ≤ L.length + M.length := by
  unfold add
  calc (normalize (L ++ M)).length ≤ (L ++ M).length := normalize_length_le _
    _ = L.length + M.length := List.length_append

theorem conv_length_le (L M : SparseFun) :
    (conv L M).length ≤ L.length * M.length := by
  unfold conv
  refine le_trans (normalize_length_le _) ?_
  induction L with
  | nil => simp
  | cons p L ih =>
    rw [List.flatMap_cons, List.length_append, List.length_map, List.length_cons,
        Nat.succ_mul]
    omega

/-! ### Arithmetic helpers for collapsing the bounds -/

theorem sortCost_mono {k k' : ℕ} (h : k ≤ k') : sortCost k ≤ sortCost k' := by
  unfold sortCost
  exact Nat.mul_le_mul (by omega) (by
    have := Nat.log_mono_right (b := 2) (by omega : k + 1 ≤ k' + 1)
    omega)

theorem sortCost_le_of_le_pow {k j : ℕ} (h : k + 1 ≤ 2 ^ j) :
    sortCost k ≤ (k + 1) * (j + 2) := by
  unfold sortCost
  refine Nat.mul_le_mul_left _ ?_
  have h1 : Nat.log 2 (k + 1) ≤ Nat.log 2 (2 ^ j) := Nat.log_mono_right h
  rw [Nat.log_pow (b := 2) (by norm_num)] at h1
  omega

theorem self_le_two_pow (n : ℕ) : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self

theorem pow_cube_le (n : ℕ) : (n + 1) ^ 3 ≤ 2 ^ (3 * n + 3) := by
  have h : n + 1 ≤ 2 ^ (n + 1) := by
    have := Nat.lt_two_pow_self (n := n + 1)
    omega
  calc (n + 1) ^ 3 ≤ (2 ^ (n + 1)) ^ 3 := Nat.pow_le_pow_left h 3
    _ = 2 ^ (3 * n + 3) := by rw [← Nat.pow_mul]; ring_nf

/-- The representation bound fits under an explicit power of two, giving a
usable bound on the logarithms in sorting costs. -/
theorem repBound_lt_two_pow (ε : ℚ) (n : ℕ) :
    repBound ε n + 1 ≤ 2 ^ (⌈1 / ε⌉₊ + 3 * n + 16) := by
  have hE : ⌈1 / ε⌉₊ + 1 ≤ 2 ^ ⌈1 / ε⌉₊ := self_le_two_pow _
  have hn : (n + 1) ^ 3 ≤ 2 ^ (3 * n + 3) := pow_cube_le n
  have h2431 : (2431 : ℕ) ≤ 2 ^ 12 := by norm_num
  unfold repBound
  have hprod : 2431 * ⌈1 / ε⌉₊ * (n + 1) ^ 3
      ≤ 2 ^ 12 * 2 ^ ⌈1 / ε⌉₊ * 2 ^ (3 * n + 3) := by
    exact Nat.mul_le_mul (Nat.mul_le_mul h2431 (by omega)) hn
  have hpow : (2 : ℕ) ^ 12 * 2 ^ ⌈1 / ε⌉₊ * 2 ^ (3 * n + 3)
      = 2 ^ (⌈1 / ε⌉₊ + 3 * n + 15) := by
    rw [← Nat.pow_add, ← Nat.pow_add]
    ring_nf
  have hone : 1 ≤ 2 ^ (⌈1 / ε⌉₊ + 3 * n + 15) := Nat.one_le_two_pow
  have hstep : 2 ^ (⌈1 / ε⌉₊ + 3 * n + 16) = 2 * 2 ^ (⌈1 / ε⌉₊ + 3 * n + 15) := by
    rw [show ⌈1 / ε⌉₊ + 3 * n + 16 = (⌈1 / ε⌉₊ + 3 * n + 15) + 1 by omega,
        Nat.pow_succ]
    omega
  omega

end SparseFun

/-! ## Cost of the insertion loop -/

namespace SparseFun

/-- Budget for one insertion, in terms of a bound `D` on the doubling
parameter and a bound `s` on the number of items. -/
def insertBudget (D s : ℕ) : ℕ :=
  5 * (1 + D * (s + 2)) + sortCost (2 * (1 + D * (s + 2))) + D * (s + 2) + 3

theorem insertBudget_mono {D D' s s' : ℕ} (hD : D ≤ D') (hs : s ≤ s') :
    insertBudget D s ≤ insertBudget D' s' := by
  unfold insertBudget
  have h1 : D * (s + 2) ≤ D' * (s' + 2) := Nat.mul_le_mul hD (by omega)
  have h2 : sortCost (2 * (1 + D * (s + 2))) ≤ sortCost (2 * (1 + D' * (s' + 2))) :=
    sortCost_mono (by omega)
  omega

theorem insertItemCost_le (δ : ℚ) (hδ : 0 < δ) (K : SparseFun) (w : ℕ)
    (D s : ℕ) (hD : doubleSteps δ ≤ D)
    (hK : K.length ≤ 1 + D * (s + 2)) (hmass : massOf K ≤ 2 ^ s) :
    insertItemCost δ K w ≤ insertBudget D s := by
  have hbumps : bumpSteps δ 1 (massOf (add K (shift w K))) ≤ D * (s + 2) := by
    have hm : massOf (add K (shift w K)) ≤ 2 ^ (s + 1) := by
      rw [massOf_add, massOf_shift, pow_succ]
      omega
    have h1 := bumpSteps_le δ hδ (massOf (add K (shift w K)))
    have h2 : Nat.log 2 (massOf (add K (shift w K))) ≤ s + 1 := by
      calc Nat.log 2 (massOf (add K (shift w K)))
          ≤ Nat.log 2 (2 ^ (s + 1)) := Nat.log_mono_right hm
        _ = s + 1 := Nat.log_pow (b := 2) (by norm_num) _
    calc bumpSteps δ 1 (massOf (add K (shift w K)))
        ≤ doubleSteps δ * (Nat.log 2 (massOf (add K (shift w K))) + 1) := h1
      _ ≤ D * ((s + 1) + 1) := Nat.mul_le_mul hD (by omega)
      _ = D * (s + 2) := by ring_nf
  have haddlen : (add K (shift w K)).length ≤ 2 * (1 + D * (s + 2)) := by
    have h := add_length_le K (shift w K)
    rw [shift_length] at h
    omega
  have hsort : sortCost (K.length + K.length)
      ≤ sortCost (2 * (1 + D * (s + 2))) :=
    sortCost_mono (by omega)
  unfold insertItemCost addCost sparsifyCost insertBudget
  rw [shift_length]
  omega

theorem halmanGoCost_le (δ : ℚ) (hδ : 0 < δ) (D s : ℕ) (hD : doubleSteps δ ≤ D) :
    ∀ S : List ℕ, S.length ≤ s →
    halmanGoCost δ S ≤ 1 + S.length * insertBudget D s := by
  intro S
  induction S with
  | nil =>
    intro _
    simp [halmanGoCost]
  | cons w S ih =>
    intro hlen
    rw [List.length_cons] at hlen
    have hK : (halmanGo δ S).length ≤ 1 + D * (s + 2) := by
      have h1 := halmanGo_length δ hδ S
      have h2 : doubleSteps δ * (S.length + 2) ≤ D * (s + 2) :=
        Nat.mul_le_mul hD (by omega)
      omega
    have hmass : massOf (halmanGo δ S) ≤ 2 ^ s := by
      have h1 := massOf_halmanGo δ S
      have h2 : (2 : ℕ) ^ S.length ≤ 2 ^ s :=
        Nat.pow_le_pow_right (by omega) (by omega)
      omega
    have hins := insertItemCost_le δ hδ (halmanGo δ S) w D s hD hK hmass
    have hrec := ih (by omega)
    show halmanGoCost δ S + insertItemCost δ (halmanGo δ S) w ≤ _
    rw [List.length_cons, Nat.succ_mul]
    omega

/-- Cost of a bottom node of the recursion tree, in global terms. -/
theorem halmanCost_le {ε : ℚ} (hε0 : 0 < ε) (n : ℕ) (S : List ℕ) (d : ℕ)
    (hd : 2 ^ d ≤ 2 * (n + 1)) (hs : (S.length - 1) * 2 ^ d ≤ n + 1) :
    halmanCost S (deltaAt ε d)
      ≤ 1 + 3 * (n + 1) * insertBudget (repBound ε n) (3 * (n + 1)) := by
  have h4d : (4 : ℕ) ^ d = 2 ^ d * 2 ^ d := by rw [← Nat.mul_pow]
  have h2d1 : 1 ≤ 2 ^ d := Nat.one_le_two_pow
  have hsub : (S.length - 1) * 2 ^ d = S.length * 2 ^ d - 1 * 2 ^ d :=
    Nat.sub_mul _ _ _
  have hs2d : S.length * 2 ^ d ≤ 3 * (n + 1) := by
    rw [hsub] at hs
    omega
  have hs3 : S.length ≤ 3 * (n + 1) := by
    have h2 : S.length * 1 ≤ S.length * 2 ^ d := Nat.mul_le_mul_left _ h2d1
    omega
  rcases Nat.eq_zero_or_pos S.length with h0 | hpos
  · have hnil : S = [] := List.length_eq_zero_iff.mp h0
    subst hnil
    show halmanGoCost _ [] ≤ _
    simp [halmanGoCost]
  · have hδ' : (0 : ℚ) < deltaAt ε d / (2 * S.length) := by
      have h1 : (0 : ℚ) < deltaAt ε d := deltaAt_pos hε0 d
      have h2 : (0 : ℚ) < (S.length : ℚ) := by exact_mod_cast hpos
      positivity
    have hE : 1 ≤ ⌈1 / ε⌉₊ := one_le_invE hε0
    have hD : doubleSteps (deltaAt ε d / (2 * S.length)) ≤ repBound ε n := by
      have h1 := doubleSteps_halman_delta hε0 d hpos
      have h2 : 81 * S.length * ⌈1 / ε⌉₊ * 4 ^ d ≤ 486 * ⌈1 / ε⌉₊ * (n + 1) ^ 2 := by
        have e1 : 81 * S.length * ⌈1 / ε⌉₊ * 4 ^ d
            = 81 * ⌈1 / ε⌉₊ * (S.length * 2 ^ d * 2 ^ d) := by
          rw [h4d]; ring
        have e2 : S.length * 2 ^ d * 2 ^ d ≤ 3 * (n + 1) * (2 * (n + 1)) :=
          Nat.mul_le_mul hs2d hd
        have e3 : 3 * (n + 1) * (2 * (n + 1)) = 6 * (n + 1) ^ 2 := by ring
        calc 81 * S.length * ⌈1 / ε⌉₊ * 4 ^ d
            = 81 * ⌈1 / ε⌉₊ * (S.length * 2 ^ d * 2 ^ d) := e1
          _ ≤ 81 * ⌈1 / ε⌉₊ * (6 * (n + 1) ^ 2) := by
              apply Nat.mul_le_mul_left
              rw [← e3]; exact e2
          _ = 486 * ⌈1 / ε⌉₊ * (n + 1) ^ 2 := by ring
      have h3 : 486 * ⌈1 / ε⌉₊ * (n + 1) ^ 2 ≤ 2431 * ⌈1 / ε⌉₊ * (n + 1) ^ 3 := by
        have hp : (n + 1) ^ 2 * 1 ≤ (n + 1) ^ 2 * (n + 1) := Nat.mul_le_mul_left _ (by omega)
        have he : (n + 1) ^ 2 * (n + 1) = (n + 1) ^ 3 := by ring
        nlinarith
      unfold repBound
      omega
    have hcost := halmanGoCost_le _ hδ' (repBound ε n) (3 * (n + 1)) hD S hs3
    have hmul : S.length * insertBudget (repBound ε n) (3 * (n + 1))
        ≤ 3 * (n + 1) * insertBudget (repBound ε n) (3 * (n + 1)) :=
      Nat.mul_le_mul_right _ hs3
    unfold halmanCost
    omega

end SparseFun

/-! ## Cost of the recursion tree -/

namespace SparseFun

/-- Per-node budget: covers a bottom node's whole insertion loop as well as
an internal node's convolution and sparsification. -/
def nodeBudget (ε : ℚ) (n : ℕ) : ℕ :=
  1 + 3 * (n + 1) * insertBudget (repBound ε n) (3 * (n + 1))
    + sortCost (repBound ε n * repBound ε n)
    + 2 * (repBound ε n * repBound ε n) + repBound ε n + 2

/-- The recursion tree on `s ≥ 1` items has at most `2s-1` nodes, each within
budget. -/
theorem dcGoCost_le {ε : ℚ} (hε0 : 0 < ε) (n T : ℕ) (S : List ℕ) (d : ℕ)
    (hd : 2 ^ d ≤ 2 * (n + 1)) (hs : (S.length - 1) * 2 ^ d ≤ n + 1)
    (hpos : 1 ≤ S.length) :
    dcGoCost ε T S d ≤ (2 * S.length - 1) * nodeBudget ε n := by
  rw [dcGoCost.eq_def]
  by_cases hlen : S.length ≤ max 1 T
  · rw [if_pos hlen]
    have hbot := halmanCost_le hε0 n S d hd hs
    have hNB : 1 + 3 * (n + 1) * insertBudget (repBound ε n) (3 * (n + 1))
        ≤ nodeBudget ε n := by
      unfold nodeBudget
      omega
    have h1 : 1 * nodeBudget ε n ≤ (2 * S.length - 1) * nodeBudget ε n :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  · rw [if_neg hlen]
    have hslen : 2 ≤ S.length := by
      have h1 : 1 ≤ max 1 T := le_max_left _ _
      omega
    have h2dn : 2 ^ d ≤ n + 1 := by
      have h1 : 1 * 2 ^ d ≤ (S.length - 1) * 2 ^ d :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    have hd' : 2 ^ (d + 1) ≤ 2 * (n + 1) := by
      rw [pow_succ]
      omega
    have hta : (S.take (S.length / 2)).length = S.length / 2 := by
      rw [List.length_take]
      omega
    have htb : (S.drop (S.length / 2)).length = S.length - S.length / 2 := by
      rw [List.length_drop]
    have hsA : ((S.take (S.length / 2)).length - 1) * 2 ^ (d + 1) ≤ n + 1 := by
      rw [hta, pow_succ]
      have e : (S.length / 2 - 1) * (2 ^ d * 2) = (2 * (S.length / 2 - 1)) * 2 ^ d := by
        ring
      rw [e]
      have h1 : 2 * (S.length / 2 - 1) ≤ S.length - 1 := by omega
      have h2 : (2 * (S.length / 2 - 1)) * 2 ^ d ≤ (S.length - 1) * 2 ^ d :=
        Nat.mul_le_mul_right _ h1
      omega
    have hsB : ((S.drop (S.length / 2)).length - 1) * 2 ^ (d + 1) ≤ n + 1 := by
      rw [htb, pow_succ]
      have e : (S.length - S.length / 2 - 1) * (2 ^ d * 2)
          = (2 * (S.length - S.length / 2 - 1)) * 2 ^ d := by
        ring
      rw [e]
      have h1 : 2 * (S.length - S.length / 2 - 1) ≤ S.length - 1 := by omega
      have h2 : (2 * (S.length - S.length / 2 - 1)) * 2 ^ d ≤ (S.length - 1) * 2 ^ d :=
        Nat.mul_le_mul_right _ h1
      omega
    have hApos : 1 ≤ (S.take (S.length / 2)).length := by rw [hta]; omega
    have hBpos : 1 ≤ (S.drop (S.length / 2)).length := by rw [htb]; omega
    have hcA := dcGoCost_le hε0 n T (S.take (S.length / 2)) (d + 1) hd' hsA hApos
    have hcB := dcGoCost_le hε0 n T (S.drop (S.length / 2)) (d + 1) hd' hsB hBpos
    have hlA := dcGo_length hε0 n T (S.take (S.length / 2)) (d + 1) hd' hsA
    have hlB := dcGo_length hε0 n T (S.drop (S.length / 2)) (d + 1) hd' hsB
    set A := dcGo ε T (S.take (S.length / 2)) (d + 1) with hA
    set B := dcGo ε T (S.drop (S.length / 2)) (d + 1) with hB
    have hAB : A.length * B.length ≤ repBound ε n * repBound ε n :=
      Nat.mul_le_mul hlA hlB
    have hconvcost : convCost A B ≤ sortCost (repBound ε n * repBound ε n)
        + repBound ε n * repBound ε n + 1 := by
      unfold convCost
      have := sortCost_mono hAB
      omega
    have hs2d : S.length * 2 ^ d ≤ 3 * (n + 1) := by
      have hsub : (S.length - 1) * 2 ^ d = S.length * 2 ^ d - 1 * 2 ^ d :=
        Nat.sub_mul _ _ _
      have h2d1 : 1 ≤ 2 ^ d := Nat.one_le_two_pow
      rw [hsub] at hs
      omega
    have hmassconv : massOf (conv A B) ≤ 2 ^ S.length := by
      rw [massOf_conv]
      calc massOf A * massOf B
          ≤ 2 ^ (S.take (S.length / 2)).length * 2 ^ (S.drop (S.length / 2)).length :=
            Nat.mul_le_mul (massOf_dcGo ε T _ _) (massOf_dcGo ε T _ _)
        _ = 2 ^ S.length := by
            rw [← pow_add, hta, htb]
            congr 1
            omega
    have hbumpsnode : bumpSteps (deltaAt ε d) 1 (massOf (conv A B)) ≤ repBound ε n := by
      have h1 := bumpSteps_le (deltaAt ε d) (deltaAt_pos hε0 d) (massOf (conv A B))
      have hlog : Nat.log 2 (massOf (conv A B)) ≤ S.length := by
        calc Nat.log 2 (massOf (conv A B)) ≤ Nat.log 2 (2 ^ S.length) :=
              Nat.log_mono_right hmassconv
          _ = S.length := Nat.log_pow (b := 2) (by norm_num) _
      have hds := doubleSteps_deltaAt hε0 d
      have hE : 1 ≤ ⌈1 / ε⌉₊ := one_le_invE hε0
      have h4d : (4 : ℕ) ^ d = 2 ^ d * 2 ^ d := by rw [← Nat.mul_pow]
      have hkey : 41 * ⌈1 / ε⌉₊ * 4 ^ d * (S.length + 1)
          ≤ 2431 * ⌈1 / ε⌉₊ * (n + 1) ^ 3 := by
        have hsp1 : S.length + 1 ≤ 2 * S.length := by omega
        have e1 : 41 * ⌈1 / ε⌉₊ * 4 ^ d * (2 * S.length)
            = 82 * ⌈1 / ε⌉₊ * (S.length * 2 ^ d * 2 ^ d) := by
          rw [h4d]; ring
        have e2 : S.length * 2 ^ d * 2 ^ d ≤ 3 * (n + 1) * (2 * (n + 1)) :=
          Nat.mul_le_mul hs2d hd
        have e3 : 3 * (n + 1) * (2 * (n + 1)) = 6 * (n + 1) ^ 2 := by ring
        have hcube : 492 * ⌈1 / ε⌉₊ * (n + 1) ^ 2 ≤ 2431 * ⌈1 / ε⌉₊ * (n + 1) ^ 3 := by
          have hp : (n + 1) ^ 2 * 1 ≤ (n + 1) ^ 2 * (n + 1) :=
            Nat.mul_le_mul_left _ (by omega)
          have he : (n + 1) ^ 2 * (n + 1) = (n + 1) ^ 3 := by ring
          nlinarith
        calc 41 * ⌈1 / ε⌉₊ * 4 ^ d * (S.length + 1)
            ≤ 41 * ⌈1 / ε⌉₊ * 4 ^ d * (2 * S.length) := Nat.mul_le_mul_left _ hsp1
          _ = 82 * ⌈1 / ε⌉₊ * (S.length * 2 ^ d * 2 ^ d) := e1
          _ ≤ 82 * ⌈1 / ε⌉₊ * (6 * (n + 1) ^ 2) := by
              apply Nat.mul_le_mul_left
              rw [← e3]; exact e2
          _ = 492 * ⌈1 / ε⌉₊ * (n + 1) ^ 2 := by ring
          _ ≤ 2431 * ⌈1 / ε⌉₊ * (n + 1) ^ 3 := hcube
      unfold repBound
      calc bumpSteps (deltaAt ε d) 1 (massOf (conv A B))
          ≤ doubleSteps (deltaAt ε d) * (Nat.log 2 (massOf (conv A B)) + 1) := h1
        _ ≤ (41 * ⌈1 / ε⌉₊ * 4 ^ d) * (S.length + 1) := Nat.mul_le_mul hds (by omega)
        _ ≤ 2431 * ⌈1 / ε⌉₊ * (n + 1) ^ 3 := hkey
    have hsparcost : sparsifyCost (deltaAt ε d) (conv A B)
        ≤ repBound ε n * repBound ε n + repBound ε n + 1 := by
      unfold sparsifyCost
      have h1 : (conv A B).length ≤ repBound ε n * repBound ε n :=
        le_trans (conv_length_le A B) hAB
      omega
    have hnode : convCost A B + sparsifyCost (deltaAt ε d) (conv A B)
        ≤ nodeBudget ε n := by
      unfold nodeBudget
      omega
    have hsum : (2 * (S.length / 2) - 1) + (2 * (S.length - S.length / 2) - 1) + 1
        = 2 * S.length - 1 := by omega
    have hdist : (2 * S.length - 1) * nodeBudget ε n
        = (2 * (S.length / 2) - 1) * nodeBudget ε n
          + (2 * (S.length - S.length / 2) - 1) * nodeBudget ε n
          + 1 * nodeBudget ε n := by
      rw [← hsum, Nat.add_mul, Nat.add_mul]
    rw [hta] at hcA
    rw [htb] at hcB
    omega
termination_by S.length
decreasing_by
  · simp only [List.length_take]
    omega
  · simp only [List.length_drop]
    omega

end SparseFun

/-! ## The polynomial bound -/

namespace SparseFun

theorem pow_four_le (n : ℕ) : (n + 1) ^ 4 ≤ 2 ^ (4 * n + 4) := by
  have h : n + 1 ≤ 2 ^ (n + 1) := by
    have := Nat.lt_two_pow_self (n := n + 1)
    omega
  calc (n + 1) ^ 4 ≤ (2 ^ (n + 1)) ^ 4 := Nat.pow_le_pow_left h 4
    _ = 2 ^ (4 * n + 4) := by rw [← Nat.pow_mul]; ring_nf

set_option maxHeartbeats 1000000 in
/-- Numeric collapse: the per-node budget is at most `10⁹·⌈1/ε⌉³·(n+1)⁷`. -/
theorem nodeBudget_le {ε : ℚ} (hε0 : 0 < ε) (n : ℕ) :
    nodeBudget ε n ≤ 10 ^ 9 * ⌈1 / ε⌉₊ ^ 3 * (n + 1) ^ 7 := by
  have hE : 1 ≤ ⌈1 / ε⌉₊ := one_le_invE hε0
  have hone : ∀ k : ℕ, 1 ≤ (n + 1) ^ k := fun k => Nat.one_le_pow _ _ (by omega)
  have honeE : ∀ k : ℕ, 1 ≤ ⌈1 / ε⌉₊ ^ k := fun k => Nat.one_le_pow _ _ (by omega)
  have hEn1 : 1 ≤ ⌈1 / ε⌉₊ * (n + 1) := by
    have := Nat.mul_le_mul hE (hone 1)
    simpa using this
  have hEn : n ≤ ⌈1 / ε⌉₊ * n := by
    have := Nat.mul_le_mul_right n hE
    omega
  have hRval : repBound ε n = 2431 * (⌈1 / ε⌉₊ * (n + 1) ^ 3) := by
    unfold repBound
    ring
  have h13 : 1 ≤ ⌈1 / ε⌉₊ * (n + 1) ^ 3 := by
    have := Nat.mul_le_mul hE (hone 3)
    omega
  have h14 : 1 ≤ ⌈1 / ε⌉₊ * (n + 1) ^ 4 := by
    have := Nat.mul_le_mul hE (hone 4)
    omega
  -- Common-form conversions.
  have hc65 : ⌈1 / ε⌉₊ ^ 2 * (n + 1) ^ 6 ≤ ⌈1 / ε⌉₊ ^ 3 * (n + 1) ^ 7 := by
    have h1 : ⌈1 / ε⌉₊ ^ 2 * (n + 1) ^ 6 * 1
        ≤ ⌈1 / ε⌉₊ ^ 2 * (n + 1) ^ 6 * (⌈1 / ε⌉₊ * (n + 1)) :=
      Nat.mul_le_mul_left _ hEn1
    have h2 : ⌈1 / ε⌉₊ ^ 2 * (n + 1) ^ 6 * (⌈1 / ε⌉₊ * (n + 1))
        = ⌈1 / ε⌉₊ ^ 3 * (n + 1) ^ 7 := by ring
    omega
  have hc45 : ⌈1 / ε⌉₊ * (n + 1) ^ 4 ≤ ⌈1 / ε⌉₊ ^ 2 * (n + 1) ^ 5 := by
    have h1 : ⌈1 / ε⌉₊ * (n + 1) ^ 4 * 1
        ≤ ⌈1 / ε⌉₊ * (n + 1) ^ 4 * (⌈1 / ε⌉₊ * (n + 1)) :=
      Nat.mul_le_mul_left _ hEn1
    have h2 : ⌈1 / ε⌉₊ * (n + 1) ^ 4 * (⌈1 / ε⌉₊ * (n + 1))
        = ⌈1 / ε⌉₊ ^ 2 * (n + 1) ^ 5 := by ring
    omega
  have hc37 : ⌈1 / ε⌉₊ * (n + 1) ^ 3 ≤ ⌈1 / ε⌉₊ ^ 3 * (n + 1) ^ 7 := by
    have h0 : 1 ≤ ⌈1 / ε⌉₊ ^ 2 * (n + 1) ^ 4 := by
      have := Nat.mul_le_mul (honeE 2) (hone 4)
      omega
    have h1 : ⌈1 / ε⌉₊ * (n + 1) ^ 3 * 1
        ≤ ⌈1 / ε⌉₊ * (n + 1) ^ 3 * (⌈1 / ε⌉₊ ^ 2 * (n + 1) ^ 4) :=
      Nat.mul_le_mul_left _ h0
    have h2 : ⌈1 / ε⌉₊ * (n + 1) ^ 3 * (⌈1 / ε⌉₊ ^ 2 * (n + 1) ^ 4)
        = ⌈1 / ε⌉₊ ^ 3 * (n + 1) ^ 7 := by ring
    omega
  have hX7 : 1 ≤ ⌈1 / ε⌉₊ ^ 3 * (n + 1) ^ 7 := by
    have := Nat.mul_le_mul (honeE 3) (hone 7)
    omega
  -- (1) sortCost (R·R).
  have hR1 : repBound ε n + 1 ≤ 2 ^ (⌈1 / ε⌉₊ + 3 * n + 16) := repBound_lt_two_pow ε n
  have hsq : (repBound ε n + 1) * (repBound ε n + 1)
      = repBound ε n * repBound ε n + 2 * repBound ε n + 1 := by ring
  have hRR1 : repBound ε n * repBound ε n + 1 ≤ 2 ^ (2 * (⌈1 / ε⌉₊ + 3 * n + 16)) := by
    have h1 : repBound ε n * repBound ε n + 1
        ≤ (repBound ε n + 1) * (repBound ε n + 1) := by omega
    have h2 := Nat.mul_le_mul hR1 hR1
    have h3 : (2 : ℕ) ^ (⌈1 / ε⌉₊ + 3 * n + 16) * 2 ^ (⌈1 / ε⌉₊ + 3 * n + 16)
        = 2 ^ (2 * (⌈1 / ε⌉₊ + 3 * n + 16)) := by
      rw [← Nat.pow_add]
      ring_nf
    omega
  have hRRle : repBound ε n * repBound ε n + 1
      ≤ 5914624 * (⌈1 / ε⌉₊ ^ 2 * (n + 1) ^ 6) := by
    have h1 : repBound ε n * repBound ε n + 1
        ≤ (repBound ε n + 1) * (repBound ε n + 1) := by omega
    have h2 : repBound ε n + 1 ≤ 2432 * (⌈1 / ε⌉₊ * (n + 1) ^ 3) := by
      rw [hRval]
      omega
    have h3 := Nat.mul_le_mul h2 h2
    have h4 : 2432 * (⌈1 / ε⌉₊ * (n + 1) ^ 3) * (2432 * (⌈1 / ε⌉₊ * (n + 1) ^ 3))
        = 5914624 * (⌈1 / ε⌉₊ ^ 2 * (n + 1) ^ 6) := by ring
    omega
  have hlin1 : 2 * (⌈1 / ε⌉₊ + 3 * n + 16) + 2 ≤ 42 * (⌈1 / ε⌉₊ * (n + 1)) := by
    have hexp : 42 * (⌈1 / ε⌉₊ * (n + 1)) = 42 * (⌈1 / ε⌉₊ * n) + 42 * ⌈1 / ε⌉₊ := by
      ring
    have hEn' : n ≤ ⌈1 / ε⌉₊ * n := hEn
    omega
  have hsort1 : sortCost (repBound ε n * repBound ε n)
      ≤ 248414208 * (⌈1 / ε⌉₊ ^ 3 * (n + 1) ^ 7) := by
    have h1 := sortCost_le_of_le_pow hRR1
    have h2 := Nat.mul_le_mul hRRle hlin1
    have h3 : 5914624 * (⌈1 / ε⌉₊ ^ 2 * (n + 1) ^ 6) * (42 * (⌈1 / ε⌉₊ * (n + 1)))
        = 248414208 * (⌈1 / ε⌉₊ ^ 3 * (n + 1) ^ 7) := by ring
    omega
  -- (2) the insertion budget.
  have hY : 1 + repBound ε n * (3 * (n + 1) + 2) ≤ 12156 * (⌈1 / ε⌉₊ * (n + 1) ^ 4) := by
    have h1 : repBound ε n * (3 * (n + 1) + 2)
        ≤ 2431 * (⌈1 / ε⌉₊ * (n + 1) ^ 3) * (5 * (n + 1)) := by
      refine Nat.mul_le_mul ?_ (by omega)
      rw [hRval]
    have h2 : 2431 * (⌈1 / ε⌉₊ * (n + 1) ^ 3) * (5 * (n + 1))
        = 12155 * (⌈1 / ε⌉₊ * (n + 1) ^ 4) := by ring
    omega
  have h2Y : 2 * (1 + repBound ε n * (3 * (n + 1) + 2)) + 1
      ≤ 2 ^ (⌈1 / ε⌉₊ + 4 * n + 19) := by
    have h1 : 2 * (1 + repBound ε n * (3 * (n + 1) + 2)) + 1
        ≤ 24313 * (⌈1 / ε⌉₊ * (n + 1) ^ 4) := by omega
    have hEp : ⌈1 / ε⌉₊ ≤ 2 ^ ⌈1 / ε⌉₊ := by
      have := self_le_two_pow ⌈1 / ε⌉₊
      omega
    have hn4 : (n + 1) ^ 4 ≤ 2 ^ (4 * n + 4) := pow_four_le n
    have h2 : 24313 * (⌈1 / ε⌉₊ * (n + 1) ^ 4) ≤ 2 ^ 15 * (2 ^ ⌈1 / ε⌉₊ * 2 ^ (4 * n + 4)) :=
      Nat.mul_le_mul (by norm_num) (Nat.mul_le_mul hEp hn4)
    have h3 : (2 : ℕ) ^ 15 * (2 ^ ⌈1 / ε⌉₊ * 2 ^ (4 * n + 4)) = 2 ^ (⌈1 / ε⌉₊ + 4 * n + 19) := by
      rw [← Nat.pow_add, ← Nat.pow_add]
      ring_nf
    omega
  have hlin2 : (⌈1 / ε⌉₊ + 4 * n + 19) + 2 ≤ 26 * (⌈1 / ε⌉₊ * (n + 1)) := by
    have hexp : 26 * (⌈1 / ε⌉₊ * (n + 1)) = 26 * (⌈1 / ε⌉₊ * n) + 26 * ⌈1 / ε⌉₊ := by
      ring
    have hEn' : n ≤ ⌈1 / ε⌉₊ * n := hEn
    omega
  have hsort2 : sortCost (2 * (1 + repBound ε n * (3 * (n + 1) + 2)))
      ≤ 632138 * (⌈1 / ε⌉₊ ^ 2 * (n + 1) ^ 5) := by
    have h1 := sortCost_le_of_le_pow h2Y
    have hup : 2 * (1 + repBound ε n * (3 * (n + 1) + 2)) + 1
        ≤ 24313 * (⌈1 / ε⌉₊ * (n + 1) ^ 4) := by omega
    have h2 := Nat.mul_le_mul hup hlin2
    have h3 : 24313 * (⌈1 / ε⌉₊ * (n + 1) ^ 4) * (26 * (⌈1 / ε⌉₊ * (n + 1)))
        = 632138 * (⌈1 / ε⌉₊ ^ 2 * (n + 1) ^ 5) := by ring
    omega
  have hIB : insertBudget (repBound ε n) (3 * (n + 1))
      ≤ 710000 * (⌈1 / ε⌉₊ ^ 2 * (n + 1) ^ 5) := by
    unfold insertBudget
    have b1 : 5 * (1 + repBound ε n * (3 * (n + 1) + 2))
        ≤ 60780 * (⌈1 / ε⌉₊ * (n + 1) ^ 4) := by omega
    have hc : ⌈1 / ε⌉₊ * (n + 1) ^ 4 ≤ ⌈1 / ε⌉₊ ^ 2 * (n + 1) ^ 5 := hc45
    omega
  -- (3) assemble.
  have t1 : 3 * (n + 1) * insertBudget (repBound ε n) (3 * (n + 1))
      ≤ 2130000 * (⌈1 / ε⌉₊ ^ 3 * (n + 1) ^ 7) := by
    have h1 : 3 * (n + 1) * insertBudget (repBound ε n) (3 * (n + 1))
        ≤ 3 * (n + 1) * (710000 * (⌈1 / ε⌉₊ ^ 2 * (n + 1) ^ 5)) :=
      Nat.mul_le_mul_left _ hIB
    have h2 : 3 * (n + 1) * (710000 * (⌈1 / ε⌉₊ ^ 2 * (n + 1) ^ 5))
        = 2130000 * (⌈1 / ε⌉₊ ^ 2 * (n + 1) ^ 6) := by ring
    have h3 := Nat.mul_le_mul_left 2130000 hc65
    omega
  have t3 : 2 * (repBound ε n * repBound ε n)
      ≤ 11829248 * (⌈1 / ε⌉₊ ^ 3 * (n + 1) ^ 7) := by
    have h3 := Nat.mul_le_mul_left 11829248 hc65
    omega
  have t4 : repBound ε n ≤ 2432 * (⌈1 / ε⌉₊ ^ 3 * (n + 1) ^ 7) := by
    have h1 : repBound ε n ≤ 2432 * (⌈1 / ε⌉₊ * (n + 1) ^ 3) := by
      rw [hRval]
      omega
    have h3 := Nat.mul_le_mul_left 2432 hc37
    omega
  unfold nodeBudget
  have hgoal : (10 : ℕ) ^ 9 * ⌈1 / ε⌉₊ ^ 3 * (n + 1) ^ 7
      = 1000000000 * (⌈1 / ε⌉₊ ^ 3 * (n + 1) ^ 7) := by ring
  omega

set_option maxHeartbeats 1000000 in
/-- **The running-time theorem**: answering a #Knapsack instance costs at
most `10¹⁰ · ⌈1/ε⌉³ · (n+1)⁸` operations in the cost model - an explicit
polynomial in `n` and `1/ε`. -/
theorem approxCountCost_le (S : List ℕ) (C : ℕ) (ε : ℚ) (h0 : 0 < ε) (_h1 : ε ≤ 1) :
    approxCountCost S C ε ≤ 10 ^ 10 * ⌈1 / ε⌉₊ ^ 3 * (S.length + 1) ^ 8 := by
  have hE : 1 ≤ ⌈1 / ε⌉₊ := one_le_invE h0
  have hone : ∀ k : ℕ, 1 ≤ (S.length + 1) ^ k := fun k => Nat.one_le_pow _ _ (by omega)
  have honeE : ∀ k : ℕ, 1 ≤ ⌈1 / ε⌉₊ ^ k := fun k => Nat.one_le_pow _ _ (by omega)
  have hd0 : 2 ^ 0 ≤ 2 * (S.length + 1) := by
    rw [pow_zero]
    omega
  have hs0 : (S.length - 1) * 2 ^ 0 ≤ S.length + 1 := by
    rw [pow_zero]
    omega
  have hquery : queryCost (dc S ε) ≤ repBound ε S.length + 1 := by
    show (dc S ε).length + 1 ≤ repBound ε S.length + 1
    have := dcGo_length h0 S.length (Nat.sqrt S.length) S 0 hd0 hs0
    unfold dc
    omega
  have hX8 : 1 ≤ ⌈1 / ε⌉₊ ^ 3 * (S.length + 1) ^ 8 := by
    have := Nat.mul_le_mul (honeE 3) (hone 8)
    omega
  have hRsmall : repBound ε S.length + 1
      ≤ 2432 * (⌈1 / ε⌉₊ ^ 3 * (S.length + 1) ^ 8) := by
    have h2 : repBound ε S.length + 1 ≤ 2432 * (⌈1 / ε⌉₊ * (S.length + 1) ^ 3) := by
      unfold repBound
      have h13 : 1 ≤ ⌈1 / ε⌉₊ * (S.length + 1) ^ 3 := by
        have := Nat.mul_le_mul hE (hone 3)
        omega
      have e : 2431 * ⌈1 / ε⌉₊ * (S.length + 1) ^ 3
          = 2431 * (⌈1 / ε⌉₊ * (S.length + 1) ^ 3) := by ring
      omega
    have hconv : ⌈1 / ε⌉₊ * (S.length + 1) ^ 3
        ≤ ⌈1 / ε⌉₊ ^ 3 * (S.length + 1) ^ 8 := by
      have h0' : 1 ≤ ⌈1 / ε⌉₊ ^ 2 * (S.length + 1) ^ 5 := by
        have := Nat.mul_le_mul (honeE 2) (hone 5)
        omega
      have ha : ⌈1 / ε⌉₊ * (S.length + 1) ^ 3 * 1
          ≤ ⌈1 / ε⌉₊ * (S.length + 1) ^ 3 * (⌈1 / ε⌉₊ ^ 2 * (S.length + 1) ^ 5) :=
        Nat.mul_le_mul_left _ h0'
      have hb : ⌈1 / ε⌉₊ * (S.length + 1) ^ 3 * (⌈1 / ε⌉₊ ^ 2 * (S.length + 1) ^ 5)
          = ⌈1 / ε⌉₊ ^ 3 * (S.length + 1) ^ 8 := by ring
      omega
    have h3 := Nat.mul_le_mul_left 2432 hconv
    omega
  have hgoal : (10 : ℕ) ^ 10 * ⌈1 / ε⌉₊ ^ 3 * (S.length + 1) ^ 8
      = 10000000000 * (⌈1 / ε⌉₊ ^ 3 * (S.length + 1) ^ 8) := by ring
  rcases Nat.eq_zero_or_pos S.length with h00 | hp
  · have hzero : dcGoCost ε (Nat.sqrt S.length) S 0 = 1 := by
      rw [dcGoCost.eq_def, if_pos (by omega)]
      have hnil : S = [] := List.length_eq_zero_iff.mp h00
      rw [hnil]
      rfl
    unfold approxCountCost
    omega
  · have hcost := dcGoCost_le h0 S.length (Nat.sqrt S.length) S 0 hd0 hs0 hp
    have hnb := nodeBudget_le h0 S.length
    have h2n : (2 * S.length - 1) * nodeBudget ε S.length
        ≤ (2 * (S.length + 1)) * (10 ^ 9 * ⌈1 / ε⌉₊ ^ 3 * (S.length + 1) ^ 7) :=
      Nat.mul_le_mul (by omega) hnb
    have he : (2 * (S.length + 1)) * (10 ^ 9 * ⌈1 / ε⌉₊ ^ 3 * (S.length + 1) ^ 7)
        = 2000000000 * (⌈1 / ε⌉₊ ^ 3 * (S.length + 1) ^ 8) := by ring
    unfold approxCountCost
    omega

/-- **The FPTAS, complete**: for `0 < ε ≤ 1` the algorithm's answer is within
a factor `1+ε` of the exact count (Theorem 1) *and* is computed within an
explicit polynomial operation budget. -/
theorem fptas (S : List ℕ) (C : ℕ) (ε : ℚ) (h0 : 0 < ε) (h1 : ε ≤ 1) :
    (countLe S C ≤ approxCount S C ε ∧
      (approxCount S C ε : ℚ) ≤ (1 + ε) * countLe S C) ∧
    approxCountCost S C ε ≤ 10 ^ 10 * ⌈1 / ε⌉₊ ^ 3 * (S.length + 1) ^ 8 :=
  ⟨approxCount_spec S C ε h0 h1, approxCountCost_le S C ε h0 h1⟩

end SparseFun
