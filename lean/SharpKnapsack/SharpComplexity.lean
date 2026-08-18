/-
# The sharp cost bound: Õ(n^2.5·ε^-1.5 + n²·ε^-2)

Operation-count analysis of the sharp algorithm (`Sharp.lean`), in the cost
model of `Complexity.lean`. The result (`approxCountSharpCost_le`) matches
the paper's Theorem 1 running time term for term: writing `E = ⌈1/ε⌉`,

  cost ≤ C · LOG² · (n+1)² · (E·(√(nE)+1) + E²),

i.e. `Õ(n^2.5 ε^-1.5 + n² ε^-2)` - and the second term is dominated by the
first whenever `ε ≥ 1/n`, which is the paper's standing assumption.

The analysis: representations at depth `d` have `Õ(E·2^{d/2+D/2}·n/2^d)`
points (`dcSharpGo_length`), so one level-`d` convolution costs
`Õ(E²·2^{D-d}·n²/4^d)` per node; with `2^d` nodes a level costs
`Õ(E²·2^D·n²)` - *the same at every level* - and `D` levels plus the
balanced bottom give the bound. The tree roll-up is the multiplied-form
recurrence `2^d·cost(d) ≤ (D-d)·FLAT + 2^D·BOTC`.
-/

import SharpKnapsack.Sharp
import SharpKnapsack.Complexity

open SparseFun

namespace SparseFun

/-! ## Small generic helpers -/

/-- The sparsification scan emits at most one point per input point. -/
theorem sparsifyGo_length_le_input (δ : ℚ) :
    ∀ (rest : List (ℕ × ℕ)) (acc r : ℕ) (pending : Option (ℕ × ℕ)),
    (sparsifyGo δ rest acc r pending).length
      ≤ (if pending.isSome then 1 else 0) + rest.length := by
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
    by_cases hbr : acc + v < r
    · rw [sparsifyGo_cons_lt hbr]
      have := ih (acc + v) r pending
      simp only [List.length_cons]
      split at this <;> split <;> omega
    · match pending with
      | none =>
        rw [sparsifyGo_cons_ge_none hbr]
        have := ih (acc + v) (bumpR δ r (acc + v)) (some (p, acc))
        simp only [Option.isSome_some, ite_true, Option.isSome_none,
          List.length_cons] at this ⊢
        omega
      | some (q, base) =>
        rw [sparsifyGo_cons_ge_some hbr]
        have := ih (acc + v) (bumpR δ r (acc + v)) (some (p, acc))
        simp only [Option.isSome_some, ite_true, List.length_cons] at this ⊢
        omega

theorem sparsify_length_le_input (δ : ℚ) (L : SparseFun) :
    (sparsify δ L).length ≤ L.length := by
  have := sparsifyGo_length_le_input δ L 0 1 none
  simpa [sparsify] using this

/-- Threshold bumps advance by at least one each step. -/
theorem bumpSteps_le_target (δ : ℚ) (target : ℕ) :
    ∀ r, bumpSteps δ r target ≤ target + 1 - r := by
  intro r
  induction r using bumpSteps.induct δ target with
  | case1 r hle ih =>
    rw [bumpSteps, if_pos hle]
    have hnext : r + 1 ≤ nextR δ r := Nat.le_max_left _ _
    omega
  | case2 r hgt =>
    rw [bumpSteps_of_gt hgt]
    omega

/-- The insertion loop on at most one item produces at most two points. -/
theorem halman_length_triv {S : List ℕ} (h : S.length ≤ 1) (t : ℚ) :
    (halman S t).length ≤ 2 := by
  match S, h with
  | [], _ =>
    show (halmanGo _ []).length ≤ 2
    simp [halmanGo, emptyRep]
  | [w], _ =>
    show (insertItem _ (halmanGo _ []) w).length ≤ 2
    show (sparsify _ (add (halmanGo _ []) (shift w (halmanGo _ [])))).length ≤ 2
    refine le_trans (sparsify_length_le_input _ _) ?_
    refine le_trans (add_length_le _ _) ?_
    rw [shift_length]
    simp [halmanGo, emptyRep]

/-- The insertion loop on at most one item costs at most 32. -/
theorem halmanCost_triv {S : List ℕ} (h : S.length ≤ 1) (t : ℚ) :
    halmanCost S t ≤ 32 := by
  match S, h with
  | [], _ =>
    show halmanGoCost _ [] ≤ 32
    simp [halmanGoCost]
  | [w], _ =>
    show halmanGoCost _ [] + insertItemCost _ (halmanGo _ []) w ≤ 32
    have h1 : halmanGoCost (t / (2 * ([w] : List ℕ).length)) [] = 1 := rfl
    have h2 : (halmanGo (t / (2 * ([w] : List ℕ).length)) []).length = 1 := rfl
    set δ' := t / (2 * ([w] : List ℕ).length) with hδ'
    unfold insertItemCost addCost sparsifyCost
    have h3 : (shift w (halmanGo δ' [])).length = 1 := by
      rw [shift_length, h2]
    have h4 : (add (halmanGo δ' []) (shift w (halmanGo δ' []))).length ≤ 2 := by
      refine le_trans (add_length_le _ _) ?_
      rw [h3, h2]
    have h5 : massOf (add (halmanGo δ' []) (shift w (halmanGo δ' []))) = 2 := by
      rw [massOf_add, massOf_shift]
      show massOf emptyRep + massOf emptyRep = 2
      rw [massOf_emptyRep]
    have h6 : bumpSteps δ' 1
        (massOf (add (halmanGo δ' []) (shift w (halmanGo δ' [])))) ≤ 2 := by
      rw [h5]
      have := bumpSteps_le_target δ' 2 1
      omega
    have h7 : sortCost ((halmanGo δ' []).length + (shift w (halmanGo δ' [])).length)
        ≤ 9 := by
      rw [h2, h3]
      unfold sortCost
      have hlog : Nat.log 2 3 = 1 :=
        Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
      rw [hlog]
    omega

/-! ## Bounds on the sharp schedule's doubling parameters -/

theorem doubleSteps_deltaSharp {ε : ℚ} (hε0 : 0 < ε) (D d : ℕ) :
    doubleSteps (deltaSharp ε D d)
      ≤ 34 * ⌈1 / ε⌉₊ * (2 ^ ((d + 1) / 2) * 2 ^ ((D + 1) / 2)) := by
  have hE : 1 ≤ ⌈1 / ε⌉₊ := one_le_invE hε0
  have heq : (2 : ℚ) / deltaSharp ε D d
      = 32 * (2 ^ ((d + 1) / 2) * 2 ^ ((D + 1) / 2)) * (1 / ε) := by
    unfold deltaSharp
    field_simp
    ring
  have h1 : (1 : ℚ) / ε ≤ (⌈1 / ε⌉₊ : ℚ) := Nat.le_ceil _
  have hceil : ⌈(2 : ℚ) / deltaSharp ε D d⌉₊
      ≤ 32 * ⌈1 / ε⌉₊ * (2 ^ ((d + 1) / 2) * 2 ^ ((D + 1) / 2)) := by
    rw [Nat.ceil_le, heq]
    calc (32 : ℚ) * (2 ^ ((d + 1) / 2) * 2 ^ ((D + 1) / 2)) * (1 / ε)
        ≤ 32 * (2 ^ ((d + 1) / 2) * 2 ^ ((D + 1) / 2)) * (⌈1 / ε⌉₊ : ℚ) := by
          apply mul_le_mul_of_nonneg_left h1
          positivity
      _ = ((32 * ⌈1 / ε⌉₊ * (2 ^ ((d + 1) / 2) * 2 ^ ((D + 1) / 2)) : ℕ) : ℚ) := by
          push_cast
          ring
  have hone : 1 ≤ ⌈1 / ε⌉₊ * (2 ^ ((d + 1) / 2) * 2 ^ ((D + 1) / 2)) := by
    have h0 : (0:ℕ) < ⌈1 / ε⌉₊ * (2 ^ ((d + 1) / 2) * 2 ^ ((D + 1) / 2)) := by positivity
    omega
  unfold doubleSteps
  nlinarith

theorem doubleSteps_deltaBot {ε : ℚ} (hε0 : 0 < ε) (D : ℕ) :
    doubleSteps (deltaBot ε D)
      ≤ 34 * ⌈1 / ε⌉₊ * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2)) := by
  have hE : 1 ≤ ⌈1 / ε⌉₊ := one_le_invE hε0
  have heq : (2 : ℚ) / deltaBot ε D
      = 32 * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2)) * (1 / ε) := by
    unfold deltaBot
    field_simp
    ring
  have h1 : (1 : ℚ) / ε ≤ (⌈1 / ε⌉₊ : ℚ) := Nat.le_ceil _
  have hceil : ⌈(2 : ℚ) / deltaBot ε D⌉₊
      ≤ 32 * ⌈1 / ε⌉₊ * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2)) := by
    rw [Nat.ceil_le, heq]
    calc (32 : ℚ) * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2)) * (1 / ε)
        ≤ 32 * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2)) * (⌈1 / ε⌉₊ : ℚ) := by
          apply mul_le_mul_of_nonneg_left h1
          positivity
      _ = ((32 * ⌈1 / ε⌉₊ * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2)) : ℕ) : ℚ) := by
          push_cast
          ring
  have hone : 1 ≤ ⌈1 / ε⌉₊ * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2)) := by
    have h0 : (0:ℕ) < ⌈1 / ε⌉₊ * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2)) := by positivity
    omega
  unfold doubleSteps
  nlinarith

theorem doubleSteps_deltaBot_div {ε : ℚ} (hε0 : 0 < ε) (D : ℕ) {s : ℕ} (hs : 1 ≤ s) :
    doubleSteps (deltaBot ε D / (2 * s))
      ≤ 66 * s * ⌈1 / ε⌉₊ * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2)) := by
  have hE : 1 ≤ ⌈1 / ε⌉₊ := one_le_invE hε0
  have hδ : (0 : ℚ) < deltaBot ε D := deltaBot_pos hε0 D
  have hs' : (0 : ℚ) < (s : ℚ) := by exact_mod_cast hs
  have heq : (2 : ℚ) / (deltaBot ε D / (2 * s))
      = 64 * s * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2)) * (1 / ε) := by
    unfold deltaBot
    field_simp
    ring
  have h1 : (1 : ℚ) / ε ≤ (⌈1 / ε⌉₊ : ℚ) := Nat.le_ceil _
  have hceil : ⌈(2 : ℚ) / (deltaBot ε D / (2 * s))⌉₊
      ≤ 64 * s * ⌈1 / ε⌉₊ * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2)) := by
    rw [Nat.ceil_le, heq]
    calc (64 : ℚ) * s * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2)) * (1 / ε)
        ≤ 64 * s * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2)) * (⌈1 / ε⌉₊ : ℚ) := by
          apply mul_le_mul_of_nonneg_left h1
          positivity
      _ = ((64 * s * ⌈1 / ε⌉₊ * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2)) : ℕ) : ℚ) := by
          push_cast
          ring
  have hone : 1 ≤ s * ⌈1 / ε⌉₊ * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2)) := by
    have h0 : (0:ℕ) < s * ⌈1 / ε⌉₊ * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2)) := by
      positivity
    omega
  unfold doubleSteps
  nlinarith

/-! ## Mass and representation size through the sharp recursion -/

theorem massOf_dcSharpGo (ε : ℚ) (D : ℕ) (S : List ℕ) (d : ℕ) :
    massOf (dcSharpGo ε D S d) ≤ 2 ^ S.length := by
  rw [dcSharpGo.eq_def]
  by_cases htriv : S.length ≤ 1
  · rw [if_pos htriv]
    exact massOf_halman S _
  · rw [if_neg htriv]
    by_cases hDd : D ≤ d
    · rw [if_pos hDd]
      exact le_trans (massOf_sparsify_le _ _) (massOf_halman S _)
    · rw [if_neg hDd]
      have hA := massOf_dcSharpGo ε D (S.take (S.length / 2)) (d + 1)
      have hB := massOf_dcSharpGo ε D (S.drop (S.length / 2)) (d + 1)
      calc massOf (sparsify (deltaSharp ε D d) _)
          ≤ massOf (conv (dcSharpGo ε D (S.take (S.length / 2)) (d + 1))
              (dcSharpGo ε D (S.drop (S.length / 2)) (d + 1))) :=
            massOf_sparsify_le _ _
        _ = massOf (dcSharpGo ε D (S.take (S.length / 2)) (d + 1))
              * massOf (dcSharpGo ε D (S.drop (S.length / 2)) (d + 1)) :=
            massOf_conv _ _
        _ ≤ 2 ^ (S.take (S.length / 2)).length * 2 ^ (S.drop (S.length / 2)).length :=
            Nat.mul_le_mul hA hB
        _ = 2 ^ S.length := by
            rw [← pow_add, List.length_take, List.length_drop]
            congr 1
            omega
termination_by D - d
decreasing_by all_goals omega

/-- The per-depth representation bound:
`repSharp E n D d = 1 + 34·E·2^⌈d/2⌉·2^⌈D/2⌉·(n/2^d + 3)`. -/
def repSharp (E n D d : ℕ) : ℕ :=
  1 + 34 * E * (2 ^ ((d + 1) / 2) * 2 ^ ((D + 1) / 2)) * (n / 2 ^ d + 3)

/-- **Depth-sensitive representation bound**: the output of a depth-`d` node
has at most `repSharp` points. This is the paper's `|F_i| ≤ log_{1+δ_i} 2^{s_i}`
bound in ℕ form, and the engine of the n^2.5 analysis. -/
theorem dcSharpGo_length {ε : ℚ} (hε0 : 0 < ε) (n D : ℕ) :
    ∀ (S : List ℕ) (d : ℕ), d ≤ D → (S.length - 1) * 2 ^ d ≤ n →
    (dcSharpGo ε D S d).length ≤ repSharp ⌈1 / ε⌉₊ n D d := by
  intro S d hdD hs
  have hE : 1 ≤ ⌈1 / ε⌉₊ := one_le_invE hε0
  have hone : 1 ≤ 2 ^ ((d + 1) / 2) * 2 ^ ((D + 1) / 2) := by
    have h0 : (0:ℕ) < 2 ^ ((d + 1) / 2) * 2 ^ ((D + 1) / 2) := by positivity
    omega
  have h2d1 : 1 ≤ 2 ^ d := Nat.one_le_two_pow
  have hsn : S.length ≤ n / 2 ^ d + 1 := by
    have hsub : (S.length - 1) * 2 ^ d = S.length * 2 ^ d - 1 * 2 ^ d :=
      Nat.sub_mul _ _ _
    have hdiv := (Nat.le_div_iff_mul_le (k := 2 ^ d) (by positivity)).mpr hs
    omega
  rw [dcSharpGo.eq_def]
  by_cases htriv : S.length ≤ 1
  · rw [if_pos htriv]
    have h2 := halman_length_triv htriv (deltaBot ε D)
    unfold repSharp
    have h34 : 1 ≤ 34 * ⌈1 / ε⌉₊ := by omega
    have h3n : 1 ≤ n / 2 ^ d + 3 := by omega
    have hbig := Nat.mul_le_mul (Nat.mul_le_mul h34 hone) h3n
    omega
  · rw [if_neg htriv]
    by_cases hDd : D ≤ d
    · rw [if_pos hDd]
      obtain rfl : D = d := by omega
      have hmass : massOf (halman S (deltaBot ε D)) ≤ 2 ^ S.length :=
        massOf_halman S _
      have hlog : Nat.log 2 (massOf (halman S (deltaBot ε D))) ≤ S.length := by
        calc Nat.log 2 (massOf (halman S (deltaBot ε D)))
            ≤ Nat.log 2 (2 ^ S.length) := Nat.log_mono_right hmass
          _ = S.length := Nat.log_pow (b := 2) (by norm_num) _
      have hds := doubleSteps_deltaBot hε0 D
      calc (sparsify (deltaBot ε D) (halman S (deltaBot ε D))).length
          ≤ doubleSteps (deltaBot ε D)
              * (Nat.log 2 (massOf (halman S (deltaBot ε D))) + 1) :=
            sparsify_length _ (deltaBot_pos hε0 D) _
        _ ≤ (34 * ⌈1 / ε⌉₊ * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2)))
              * (n / 2 ^ D + 2) := by
            refine Nat.mul_le_mul hds ?_
            omega
        _ ≤ repSharp ⌈1 / ε⌉₊ n D D := by
            unfold repSharp
            have := Nat.mul_le_mul_left
              (34 * ⌈1 / ε⌉₊ * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2)))
              (show n / 2 ^ D + 2 ≤ n / 2 ^ D + 3 by omega)
            omega
    · rw [if_neg hDd]
      set A := dcSharpGo ε D (S.take (S.length / 2)) (d + 1)
      set B := dcSharpGo ε D (S.drop (S.length / 2)) (d + 1)
      have hmass : massOf (conv A B) ≤ 2 ^ S.length := by
        rw [massOf_conv]
        calc massOf A * massOf B
            ≤ 2 ^ (S.take (S.length / 2)).length * 2 ^ (S.drop (S.length / 2)).length :=
              Nat.mul_le_mul (massOf_dcSharpGo ε D _ _) (massOf_dcSharpGo ε D _ _)
          _ = 2 ^ S.length := by
              rw [← pow_add, List.length_take, List.length_drop]
              congr 1
              omega
      have hlog : Nat.log 2 (massOf (conv A B)) ≤ S.length := by
        calc Nat.log 2 (massOf (conv A B)) ≤ Nat.log 2 (2 ^ S.length) :=
              Nat.log_mono_right hmass
          _ = S.length := Nat.log_pow (b := 2) (by norm_num) _
      have hds := doubleSteps_deltaSharp hε0 D d
      calc (sparsify (deltaSharp ε D d) (conv A B)).length
          ≤ doubleSteps (deltaSharp ε D d) * (Nat.log 2 (massOf (conv A B)) + 1) :=
            sparsify_length _ (deltaSharp_pos hε0 D d) _
        _ ≤ (34 * ⌈1 / ε⌉₊ * (2 ^ ((d + 1) / 2) * 2 ^ ((D + 1) / 2)))
              * (n / 2 ^ d + 2) := by
            refine Nat.mul_le_mul hds ?_
            omega
        _ ≤ repSharp ⌈1 / ε⌉₊ n D d := by
            unfold repSharp
            have := Nat.mul_le_mul_left
              (34 * ⌈1 / ε⌉₊ * (2 ^ ((d + 1) / 2) * 2 ^ ((D + 1) / 2)))
              (show n / 2 ^ d + 2 ≤ n / 2 ^ d + 3 by omega)
            omega

/-! ## The cost of the sharp algorithm -/

def dcSharpGoCost (ε : ℚ) (D : ℕ) (S : List ℕ) (d : ℕ) : ℕ :=
  if S.length ≤ 1 then
    halmanCost S (deltaBot ε D)
  else if D ≤ d then
    halmanCost S (deltaBot ε D)
      + sparsifyCost (deltaBot ε D) (halman S (deltaBot ε D))
  else
    dcSharpGoCost ε D (S.take (S.length / 2)) (d + 1) +
    dcSharpGoCost ε D (S.drop (S.length / 2)) (d + 1) +
    convCost (dcSharpGo ε D (S.take (S.length / 2)) (d + 1))
             (dcSharpGo ε D (S.drop (S.length / 2)) (d + 1)) +
    sparsifyCost (deltaSharp ε D d)
      (conv (dcSharpGo ε D (S.take (S.length / 2)) (d + 1))
            (dcSharpGo ε D (S.drop (S.length / 2)) (d + 1)))
termination_by D - d
decreasing_by all_goals omega

def approxCountSharpCost (S : List ℕ) (_C : ℕ) (ε : ℚ) : ℕ :=
  dcSharpGoCost ε (sharpDepth S.length ⌈1 / ε⌉₊) S 0 + queryCost (dcSharp S ε)

/-! ## The log factor and power-chain helpers -/

/-- The polylog factor of the sharp bound. -/
def LGsharp (E n D : ℕ) : ℕ :=
  2 * Nat.log 2 (E + 1) + 4 * D + 4 * Nat.log 2 (n + 2) + 40

theorem le_LGsharp_pow (E n D k : ℕ)
    (h : k + 1 ≤ 2 ^ (LGsharp E n D - 2)) :
    sortCost k ≤ (k + 1) * LGsharp E n D := by
  have h1 := sortCost_le_of_le_pow h
  have h2 : LGsharp E n D - 2 + 2 = LGsharp E n D := by
    unfold LGsharp
    omega
  calc sortCost k ≤ (k + 1) * (LGsharp E n D - 2 + 2) := h1
    _ = (k + 1) * LGsharp E n D := by rw [h2]

theorem self_le_pow_log (x : ℕ) : x + 1 ≤ 2 ^ (Nat.log 2 (x + 1) + 1) := by
  have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (x + 1)
  omega

/-- The generic power-domination fact used to feed `sortCost` bounds:
`c·E^a·pow·(n-part) + 1 ≤ 2^(LGsharp-2)` instances are all proven through
this chain. -/
theorem prod_le_two_pow {a b c i j k : ℕ}
    (ha : a ≤ 2 ^ i) (hb : b ≤ 2 ^ j) (hc : c ≤ 2 ^ k) :
    a * b * c ≤ 2 ^ (i + j + k) := by
  calc a * b * c ≤ 2 ^ i * 2 ^ j * 2 ^ k :=
        Nat.mul_le_mul (Nat.mul_le_mul ha hb) hc
    _ = 2 ^ (i + j + k) := by rw [← Nat.pow_add, ← Nat.pow_add]

/-! ## Cost of a depth-`D` bottom node -/

/-- Per-bottom-node cost cap. -/
def BOTC (E n D LG : ℕ) : ℕ :=
  300 * LG * E * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2)) * (n / 2 ^ D + 3) ^ 3 + 64

/-- Pure-arithmetic collapse of the insertion budget (no rationals: all
products appear literally so `omega` can treat them as atoms). Here
`W = Dh·(s+2)` with `Dh = 66·s·E·PP` the doubling bound, and
`X = E·PP·(s+2)²`. -/
theorem insertBudget_le_sharp (E PP LG s : ℕ) (hE : 1 ≤ E) (hPP : 1 ≤ PP)
    (hLG : 40 ≤ LG)
    (hsort : sortCost (2 * (1 + 66 * s * E * PP * (s + 2)))
      ≤ (2 * (1 + 66 * s * E * PP * (s + 2)) + 1) * LG) :
    insertBudget (66 * s * E * PP) s ≤ 215 * LG * (E * PP * (s + 2) ^ 2) := by
  unfold insertBudget
  have hone : 1 ≤ E * PP * (s + 2) ^ 2 := by
    have h0 : (0:ℕ) < E * PP * (s + 2) ^ 2 := by positivity
    omega
  have hW : 66 * s * E * PP * (s + 2) ≤ 66 * (E * PP * (s + 2) ^ 2) := by
    have e : 66 * s * E * PP * (s + 2) = 66 * (E * PP) * (s * (s + 2)) := by ring
    have h : s * (s + 2) ≤ (s + 2) ^ 2 := by nlinarith
    calc 66 * s * E * PP * (s + 2) = 66 * (E * PP) * (s * (s + 2)) := e
      _ ≤ 66 * (E * PP) * (s + 2) ^ 2 := Nat.mul_le_mul_left _ h
      _ = 66 * (E * PP * (s + 2) ^ 2) := by ring
  have hXLG : E * PP * (s + 2) ^ 2 ≤ E * PP * (s + 2) ^ 2 * LG :=
    Nat.le_mul_of_pos_right _ (by omega)
  have harg : 2 * (1 + 66 * s * E * PP * (s + 2)) + 1
      ≤ 137 * (E * PP * (s + 2) ^ 2) := by omega
  have hsort2 : sortCost (2 * (1 + 66 * s * E * PP * (s + 2)))
      ≤ 137 * (E * PP * (s + 2) ^ 2 * LG) := by
    calc sortCost (2 * (1 + 66 * s * E * PP * (s + 2)))
        ≤ (2 * (1 + 66 * s * E * PP * (s + 2)) + 1) * LG := hsort
      _ ≤ 137 * (E * PP * (s + 2) ^ 2) * LG := Nat.mul_le_mul_right _ harg
      _ = 137 * (E * PP * (s + 2) ^ 2 * LG) := by ring
  have hsmall : 405 * (E * PP * (s + 2) ^ 2) ≤ 78 * (E * PP * (s + 2) ^ 2 * LG) := by
    have h1 : 405 ≤ 78 * LG := by omega
    calc 405 * (E * PP * (s + 2) ^ 2)
        ≤ 78 * LG * (E * PP * (s + 2) ^ 2) :=
          Nat.mul_le_mul_right _ h1
      _ = 78 * (E * PP * (s + 2) ^ 2 * LG) := by ring
  have hfin : 215 * LG * (E * PP * (s + 2) ^ 2)
      = 137 * (E * PP * (s + 2) ^ 2 * LG) + 78 * (E * PP * (s + 2) ^ 2 * LG) := by
    ring
  omega

/-- The sort argument of a bottom node fits under the log factor. -/
theorem bottom_sort_arg {E n D s : ℕ} (hE : 1 ≤ E) (hs : s ≤ n + 1) :
    2 * (1 + 66 * s * E * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2)) * (s + 2)) + 1
      ≤ 2 ^ (LGsharp E n D - 2) := by
  have hPP : (2:ℕ) ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2) ≤ 2 ^ (D + 1) := by
    rw [← Nat.pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hEp : E ≤ 2 ^ (Nat.log 2 (E + 1) + 1) := by
    have := self_le_pow_log E
    omega
  have hnp : n + 2 ≤ 2 ^ (Nat.log 2 (n + 2) + 1) := by
    have := self_le_pow_log (n + 1)
    have e : n + 1 + 1 = n + 2 := by omega
    rw [e] at this
    exact this
  have hs3 : s + 2 ≤ (n + 2) * 2 := by omega
  have hs2 : s ≤ (n + 2) * 2 := by omega
  -- LHS ≤ 2·(1 + 66·s·E·2^{D+1}·(s+2)) + 1 ≤ 201·s·E·2^{D+1}·(s+2) + 3-ish,
  -- then power-dominate each factor.
  have hbig : 2 * (1 + 66 * s * E * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2)) * (s + 2)) + 1
      ≤ 512 * (s + 2) * E * 2 ^ (D + 1) * (s + 2) := by
    have h1 : 66 * s * E * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2)) * (s + 2)
        ≤ 66 * (s + 2) * E * 2 ^ (D + 1) * (s + 2) := by
      have h2 : 66 * s * E ≤ 66 * (s + 2) * E := by
        have := Nat.mul_le_mul_right E
          (Nat.mul_le_mul_left 66 (show s ≤ s + 2 by omega))
        omega
      calc 66 * s * E * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2)) * (s + 2)
          ≤ 66 * (s + 2) * E * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2)) * (s + 2) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h2)
        _ ≤ 66 * (s + 2) * E * 2 ^ (D + 1) * (s + 2) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hPP)
    have hone : 1 ≤ (s + 2) * E * 2 ^ (D + 1) * (s + 2) := by
      have h0 : (0:ℕ) < (s + 2) * E * 2 ^ (D + 1) * (s + 2) := by positivity
      omega
    have e1 : 512 * (s + 2) * E * 2 ^ (D + 1) * (s + 2)
        = 512 * ((s + 2) * E * 2 ^ (D + 1) * (s + 2)) := by ring
    have e2 : 66 * (s + 2) * E * 2 ^ (D + 1) * (s + 2)
        = 66 * ((s + 2) * E * 2 ^ (D + 1) * (s + 2)) := by ring
    omega
  refine le_trans hbig ?_
  -- 512·(s+2)·E·2^{D+1}·(s+2) ≤ 2^{9 + (log(n+2)+2) + (log(E+1)+1) + (D+1) + (log(n+2)+2)}
  have hsp : s + 2 ≤ 2 ^ (Nat.log 2 (n + 2) + 2) := by
    calc s + 2 ≤ (n + 2) * 2 := hs3
      _ ≤ 2 ^ (Nat.log 2 (n + 2) + 1) * 2 := Nat.mul_le_mul_right _ hnp
      _ = 2 ^ (Nat.log 2 (n + 2) + 2) :=
          (Nat.pow_succ 2 (Nat.log 2 (n + 2) + 1)).symm
  have h512 : (512 : ℕ) ≤ 2 ^ 9 := by norm_num
  have hchain : 512 * (s + 2) * E * 2 ^ (D + 1) * (s + 2)
      ≤ 2 ^ (9 + (Nat.log 2 (n + 2) + 2) + (Nat.log 2 (E + 1) + 1) + (D + 1)
          + (Nat.log 2 (n + 2) + 2)) := by
    calc 512 * (s + 2) * E * 2 ^ (D + 1) * (s + 2)
        ≤ 2 ^ 9 * 2 ^ (Nat.log 2 (n + 2) + 2) * 2 ^ (Nat.log 2 (E + 1) + 1)
            * 2 ^ (D + 1) * 2 ^ (Nat.log 2 (n + 2) + 2) :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul
            (Nat.mul_le_mul h512 hsp) hEp) le_rfl) hsp
      _ = 2 ^ (9 + (Nat.log 2 (n + 2) + 2) + (Nat.log 2 (E + 1) + 1) + (D + 1)
            + (Nat.log 2 (n + 2) + 2)) := by
          rw [← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add]
  refine le_trans hchain (Nat.pow_le_pow_right (by norm_num) ?_)
  unfold LGsharp
  omega

set_option maxHeartbeats 1000000 in
/-- Cost of a depth-`D` bottom node. -/
theorem bottomCost_le {ε : ℚ} (hε0 : 0 < ε) (n D : ℕ) (S : List ℕ)
    (hσ : S.length ≤ n / 2 ^ D + 1) (h2 : 2 ≤ S.length) :
    halmanCost S (deltaBot ε D)
        + sparsifyCost (deltaBot ε D) (halman S (deltaBot ε D))
      ≤ BOTC ⌈1 / ε⌉₊ n D (LGsharp ⌈1 / ε⌉₊ n D) := by
  have hE : 1 ≤ ⌈1 / ε⌉₊ := one_le_invE hε0
  have hPP : 1 ≤ (2:ℕ) ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2) := by
    have h0 : (0:ℕ) < (2:ℕ) ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2) := by positivity
    omega
  have hLG : 40 ≤ LGsharp ⌈1 / ε⌉₊ n D := by
    unfold LGsharp
    omega
  have hs1 : 1 ≤ S.length := by omega
  have hδ' : (0 : ℚ) < deltaBot ε D / (2 * S.length) := by
    have h1 := deltaBot_pos hε0 D
    have h2' : (0 : ℚ) < (S.length : ℚ) := by exact_mod_cast hs1
    positivity
  have hsn : S.length ≤ n + 1 := by
    have := Nat.div_le_self n (2 ^ D)
    omega
  -- The insertion loop.
  have hDh := doubleSteps_deltaBot_div hε0 D (s := S.length) hs1
  have hsort := le_LGsharp_pow ⌈1 / ε⌉₊ n D
    (2 * (1 + 66 * S.length * ⌈1 / ε⌉₊
      * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2)) * (S.length + 2)))
    (bottom_sort_arg hE hsn)
  have hIB := insertBudget_le_sharp ⌈1 / ε⌉₊
    (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2)) (LGsharp ⌈1 / ε⌉₊ n D) S.length
    hE hPP hLG hsort
  have hcost := halmanGoCost_le _ hδ'
    (66 * S.length * ⌈1 / ε⌉₊ * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2)))
    S.length hDh S le_rfl
  -- The re-sparsification.
  have hout_len : (halman S (deltaBot ε D)).length
      ≤ 1 + 66 * S.length * ⌈1 / ε⌉₊
          * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2)) * (S.length + 2) := by
    have h1 := halmanGo_length _ hδ' S
    have h2' := Nat.mul_le_mul hDh (le_refl (S.length + 2))
    unfold halman
    omega
  have hbumps : bumpSteps (deltaBot ε D) 1 (massOf (halman S (deltaBot ε D)))
      ≤ 34 * ⌈1 / ε⌉₊ * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2)) * (S.length + 1) := by
    have h1 := bumpSteps_le (deltaBot ε D) (deltaBot_pos hε0 D)
      (massOf (halman S (deltaBot ε D)))
    have hmass : massOf (halman S (deltaBot ε D)) ≤ 2 ^ S.length := massOf_halman S _
    have hlog : Nat.log 2 (massOf (halman S (deltaBot ε D))) ≤ S.length := by
      calc Nat.log 2 (massOf (halman S (deltaBot ε D)))
          ≤ Nat.log 2 (2 ^ S.length) := Nat.log_mono_right hmass
        _ = S.length := Nat.log_pow (b := 2) (by norm_num) _
    have hds := doubleSteps_deltaBot hε0 D
    calc bumpSteps (deltaBot ε D) 1 (massOf (halman S (deltaBot ε D)))
        ≤ doubleSteps (deltaBot ε D)
            * (Nat.log 2 (massOf (halman S (deltaBot ε D))) + 1) := h1
      _ ≤ 34 * ⌈1 / ε⌉₊ * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2)) * (S.length + 1) :=
          Nat.mul_le_mul hds (by omega)
  -- Pure-ℕ final collapse.
  have hσ3 : S.length + 2 ≤ n / 2 ^ D + 3 := by omega
  have hcube : S.length * (⌈1 / ε⌉₊ * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2))
        * (S.length + 2) ^ 2) ≤ ⌈1 / ε⌉₊ * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2))
        * (n / 2 ^ D + 3) ^ 3 := by
    have e1 : S.length * (⌈1 / ε⌉₊ * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2))
        * (S.length + 2) ^ 2) = ⌈1 / ε⌉₊ * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2))
        * (S.length * (S.length + 2) ^ 2) := by ring
    have h1 : S.length * (S.length + 2) ^ 2 ≤ (n / 2 ^ D + 3) ^ 3 := by
      calc S.length * (S.length + 2) ^ 2
          ≤ (S.length + 2) * (S.length + 2) ^ 2 := Nat.mul_le_mul_right _ (by omega)
        _ = (S.length + 2) ^ 3 := by ring
        _ ≤ (n / 2 ^ D + 3) ^ 3 := Nat.pow_le_pow_left hσ3 3
    rw [e1]
    exact Nat.mul_le_mul_left _ h1
  have hsq : (⌈1 / ε⌉₊ * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2)) * (S.length + 2) ^ 2)
      ≤ ⌈1 / ε⌉₊ * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2)) * (n / 2 ^ D + 3) ^ 3 := by
    refine Nat.mul_le_mul_left _ ?_
    calc (S.length + 2) ^ 2 ≤ (S.length + 2) ^ 3 :=
          Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ (n / 2 ^ D + 3) ^ 3 := Nat.pow_le_pow_left hσ3 3
  have hlin : S.length + 1 ≤ (n / 2 ^ D + 3) ^ 3 := by
    have h1 : S.length + 1 ≤ (n / 2 ^ D + 3) := by omega
    calc S.length + 1 ≤ n / 2 ^ D + 3 := h1
      _ ≤ (n / 2 ^ D + 3) ^ 3 := Nat.le_self_pow (by omega) _
  -- Assemble.
  unfold BOTC halmanCost at *
  -- name the recurring atoms via generalization
  have hIB' := Nat.mul_le_mul_left S.length hIB
  -- halmanCost ≤ 1 + s·IB ≤ 1 + 215·LG·(E·PP·σ³)
  have hterm1 : S.length * (215 * LGsharp ⌈1 / ε⌉₊ n D
      * (⌈1 / ε⌉₊ * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2)) * (S.length + 2) ^ 2))
      ≤ 215 * LGsharp ⌈1 / ε⌉₊ n D * (⌈1 / ε⌉₊
          * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2)) * (n / 2 ^ D + 3) ^ 3) := by
    have e1 : S.length * (215 * LGsharp ⌈1 / ε⌉₊ n D
        * (⌈1 / ε⌉₊ * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2)) * (S.length + 2) ^ 2))
        = 215 * LGsharp ⌈1 / ε⌉₊ n D * (S.length * (⌈1 / ε⌉₊
            * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2)) * (S.length + 2) ^ 2)) := by
      ring
    rw [e1]
    exact Nat.mul_le_mul_left _ hcube
  have hbump2 : 34 * ⌈1 / ε⌉₊ * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2)) * (S.length + 1)
      ≤ 34 * (⌈1 / ε⌉₊ * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2)) * (n / 2 ^ D + 3) ^ 3) := by
    have e1 : 34 * ⌈1 / ε⌉₊ * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2)) * (S.length + 1)
        = 34 * (⌈1 / ε⌉₊ * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2)) * (S.length + 1)) := by
      ring
    rw [e1]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hlin)
  have hout2 : 66 * S.length * ⌈1 / ε⌉₊ * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2))
      * (S.length + 2) ≤ 66 * (⌈1 / ε⌉₊ * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2))
      * (n / 2 ^ D + 3) ^ 3) := by
    have e1 : 66 * S.length * ⌈1 / ε⌉₊ * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2))
        * (S.length + 2)
        = 66 * (⌈1 / ε⌉₊ * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2))
            * (S.length * (S.length + 2))) := by
      ring
    have h1 : S.length * (S.length + 2) ≤ (n / 2 ^ D + 3) ^ 3 := by
      calc S.length * (S.length + 2) ≤ (S.length + 2) * (S.length + 2) :=
            Nat.mul_le_mul_right _ (by omega)
        _ = (S.length + 2) ^ 2 := by ring
        _ ≤ (S.length + 2) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
        _ ≤ (n / 2 ^ D + 3) ^ 3 := Nat.pow_le_pow_left hσ3 3
    rw [e1]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h1)
  -- Final assembly.
  unfold sparsifyCost
  have e300 : 300 * LGsharp ⌈1 / ε⌉₊ n D * ⌈1 / ε⌉₊
      * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2)) * (n / 2 ^ D + 3) ^ 3
      = 215 * LGsharp ⌈1 / ε⌉₊ n D * (⌈1 / ε⌉₊
          * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2)) * (n / 2 ^ D + 3) ^ 3)
        + 85 * LGsharp ⌈1 / ε⌉₊ n D * (⌈1 / ε⌉₊
          * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2)) * (n / 2 ^ D + 3) ^ 3) := by
    ring
  have hsmall : 100 * (⌈1 / ε⌉₊ * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2))
      * (n / 2 ^ D + 3) ^ 3)
      ≤ 85 * LGsharp ⌈1 / ε⌉₊ n D * (⌈1 / ε⌉₊
          * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2)) * (n / 2 ^ D + 3) ^ 3) := by
    have h1 : (100 : ℕ) ≤ 85 * LGsharp ⌈1 / ε⌉₊ n D := by omega
    exact Nat.mul_le_mul_right _ h1
  omega

/-! ## Internal nodes: one level costs a flat amount -/

/-- The flat per-level budget (times `2^d` this dominates any internal
node's cost at depth `d`). -/
def FLAT (E n D LG : ℕ) : ℕ :=
  5000 * (LG + 3) * E * E * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2))
    * (n + 3 * 2 ^ D + 4) ^ 2

/-- The sort argument of an internal node fits under the log factor. -/
theorem internal_sort_arg {E n D d : ℕ} (hE : 1 ≤ E) (hd : d < D) :
    repSharp E n D (d + 1) * repSharp E n D (d + 1) + 1
      ≤ 2 ^ (LGsharp E n D - 2) := by
  have hEp : E ≤ 2 ^ (Nat.log 2 (E + 1) + 1) := by
    have := self_le_pow_log E
    omega
  have hnp : n + 2 ≤ 2 ^ (Nat.log 2 (n + 2) + 1) := by
    have := self_le_pow_log (n + 1)
    have e : n + 1 + 1 = n + 2 := by omega
    rw [e] at this
    exact this
  have hpow1 : (2:ℕ) ^ ((d + 1 + 1) / 2) ≤ 2 ^ (D + 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpow2 : (2:ℕ) ^ ((D + 1) / 2) ≤ 2 ^ (D + 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hdiv : n / 2 ^ (d + 1) + 3 ≤ (n + 2) * 4 := by
    have := Nat.div_le_self n (2 ^ (d + 1))
    omega
  have hR : repSharp E n D (d + 1)
      ≤ 2 ^ (6 + (Nat.log 2 (E + 1) + 1) + (D + 1) + (D + 1)
          + (Nat.log 2 (n + 2) + 3)) := by
    unfold repSharp
    have h35 : 1 + 34 * E * (2 ^ ((d + 1 + 1) / 2) * 2 ^ ((D + 1) / 2))
        * (n / 2 ^ (d + 1) + 3)
        ≤ 64 * E * (2 ^ ((d + 1 + 1) / 2) * 2 ^ ((D + 1) / 2))
          * (n / 2 ^ (d + 1) + 3) := by
      have hone : 1 ≤ E * (2 ^ ((d + 1 + 1) / 2) * 2 ^ ((D + 1) / 2))
          * (n / 2 ^ (d + 1) + 3) := by
        have h0 : (0:ℕ) < E * (2 ^ ((d + 1 + 1) / 2) * 2 ^ ((D + 1) / 2))
            * (n / 2 ^ (d + 1) + 3) := by positivity
        omega
      have e1 : 64 * E * (2 ^ ((d + 1 + 1) / 2) * 2 ^ ((D + 1) / 2))
          * (n / 2 ^ (d + 1) + 3)
          = 34 * (E * (2 ^ ((d + 1 + 1) / 2) * 2 ^ ((D + 1) / 2))
              * (n / 2 ^ (d + 1) + 3))
            + 30 * (E * (2 ^ ((d + 1 + 1) / 2) * 2 ^ ((D + 1) / 2))
              * (n / 2 ^ (d + 1) + 3)) := by ring
      have e2 : 34 * E * (2 ^ ((d + 1 + 1) / 2) * 2 ^ ((D + 1) / 2))
          * (n / 2 ^ (d + 1) + 3)
          = 34 * (E * (2 ^ ((d + 1 + 1) / 2) * 2 ^ ((D + 1) / 2))
              * (n / 2 ^ (d + 1) + 3)) := by ring
      omega
    have hn4 : n / 2 ^ (d + 1) + 3 ≤ 2 ^ (Nat.log 2 (n + 2) + 3) := by
      have e1 : (2:ℕ) ^ (Nat.log 2 (n + 2) + 3)
          = 2 ^ (Nat.log 2 (n + 2) + 1) * 4 := by
        rw [show Nat.log 2 (n + 2) + 3 = (Nat.log 2 (n + 2) + 1) + 2 by omega,
          Nat.pow_add]
      have h2 : (n + 2) * 4 ≤ 2 ^ (Nat.log 2 (n + 2) + 1) * 4 :=
        Nat.mul_le_mul_right _ hnp
      omega
    have h64 : (64:ℕ) ≤ 2 ^ 6 := by norm_num
    calc 1 + 34 * E * (2 ^ ((d + 1 + 1) / 2) * 2 ^ ((D + 1) / 2))
        * (n / 2 ^ (d + 1) + 3)
        ≤ 64 * E * (2 ^ ((d + 1 + 1) / 2) * 2 ^ ((D + 1) / 2))
          * (n / 2 ^ (d + 1) + 3) := h35
      _ ≤ 2 ^ 6 * 2 ^ (Nat.log 2 (E + 1) + 1) * (2 ^ (D + 1) * 2 ^ (D + 1))
          * 2 ^ (Nat.log 2 (n + 2) + 3) :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h64 hEp)
            (Nat.mul_le_mul hpow1 hpow2)) hn4
      _ = 2 ^ (6 + (Nat.log 2 (E + 1) + 1) + (D + 1) + (D + 1)
          + (Nat.log 2 (n + 2) + 3)) := by
          rw [← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add]
          congr 1
          ring
  have hRR : repSharp E n D (d + 1) * repSharp E n D (d + 1) + 1
      ≤ 2 ^ (2 * (6 + (Nat.log 2 (E + 1) + 1) + (D + 1) + (D + 1)
          + (Nat.log 2 (n + 2) + 3)) + 1) := by
    have h1 := Nat.mul_le_mul hR hR
    have h2 : (2:ℕ) ^ (6 + (Nat.log 2 (E + 1) + 1) + (D + 1) + (D + 1)
          + (Nat.log 2 (n + 2) + 3))
        * 2 ^ (6 + (Nat.log 2 (E + 1) + 1) + (D + 1) + (D + 1)
          + (Nat.log 2 (n + 2) + 3))
        = 2 ^ (2 * (6 + (Nat.log 2 (E + 1) + 1) + (D + 1) + (D + 1)
          + (Nat.log 2 (n + 2) + 3))) := by
      rw [← Nat.pow_add]
      congr 1
      ring
    have h3 : (0:ℕ) < 2 ^ (2 * (6 + (Nat.log 2 (E + 1) + 1) + (D + 1) + (D + 1)
        + (Nat.log 2 (n + 2) + 3))) := by positivity
    have h4 : (2:ℕ) ^ (2 * (6 + (Nat.log 2 (E + 1) + 1) + (D + 1) + (D + 1)
          + (Nat.log 2 (n + 2) + 3)) + 1)
        = 2 ^ (2 * (6 + (Nat.log 2 (E + 1) + 1) + (D + 1) + (D + 1)
          + (Nat.log 2 (n + 2) + 3))) * 2 := Nat.pow_succ 2 _
    omega
  refine le_trans hRR (Nat.pow_le_pow_right (by norm_num) ?_)
  unfold LGsharp
  omega

set_option maxHeartbeats 1000000 in
/-- One internal node's cost, multiplied by `2^d`, fits in the flat budget. -/
theorem internal_node_flat {ε : ℚ} (hε0 : 0 < ε) (n D d : ℕ) (A B : SparseFun)
    (hd : d < D)
    (hA : A.length ≤ repSharp ⌈1 / ε⌉₊ n D (d + 1))
    (hB : B.length ≤ repSharp ⌈1 / ε⌉₊ n D (d + 1))
    (hbump : bumpSteps (deltaSharp ε D d) 1 (massOf (conv A B))
      ≤ 34 * ⌈1 / ε⌉₊ * (2 ^ ((d + 1) / 2) * 2 ^ ((D + 1) / 2)) * (n / 2 ^ d + 2)) :
    2 ^ d * (convCost A B + sparsifyCost (deltaSharp ε D d) (conv A B))
      ≤ FLAT ⌈1 / ε⌉₊ n D (LGsharp ⌈1 / ε⌉₊ n D) := by
  have hE : 1 ≤ ⌈1 / ε⌉₊ := one_le_invE hε0
  have hLG : 40 ≤ LGsharp ⌈1 / ε⌉₊ n D := by
    unfold LGsharp
    omega
  have hRR := Nat.mul_le_mul hA hB
  have hsort := le_LGsharp_pow ⌈1 / ε⌉₊ n D
    (repSharp ⌈1 / ε⌉₊ n D (d + 1) * repSharp ⌈1 / ε⌉₊ n D (d + 1))
    (internal_sort_arg hE hd)
  have hconvlen := conv_length_le A B
  -- node ≤ (LG+3)·(R² + 1) + bump-term
  have hnode : convCost A B + sparsifyCost (deltaSharp ε D d) (conv A B)
      ≤ (LGsharp ⌈1 / ε⌉₊ n D + 3)
          * (repSharp ⌈1 / ε⌉₊ n D (d + 1) * repSharp ⌈1 / ε⌉₊ n D (d + 1) + 1)
        + 34 * ⌈1 / ε⌉₊ * (2 ^ ((d + 1) / 2) * 2 ^ ((D + 1) / 2)) * (n / 2 ^ d + 2) := by
    unfold convCost sparsifyCost
    have h1 : sortCost (A.length * B.length)
        ≤ (repSharp ⌈1 / ε⌉₊ n D (d + 1) * repSharp ⌈1 / ε⌉₊ n D (d + 1) + 1)
          * LGsharp ⌈1 / ε⌉₊ n D := by
      calc sortCost (A.length * B.length)
          ≤ sortCost (repSharp ⌈1 / ε⌉₊ n D (d + 1) * repSharp ⌈1 / ε⌉₊ n D (d + 1)) :=
            sortCost_mono hRR
        _ ≤ (repSharp ⌈1 / ε⌉₊ n D (d + 1) * repSharp ⌈1 / ε⌉₊ n D (d + 1) + 1)
              * LGsharp ⌈1 / ε⌉₊ n D := hsort
    have h2 : (conv A B).length
        ≤ repSharp ⌈1 / ε⌉₊ n D (d + 1) * repSharp ⌈1 / ε⌉₊ n D (d + 1) :=
      le_trans hconvlen hRR
    have e1 : (LGsharp ⌈1 / ε⌉₊ n D + 3)
        * (repSharp ⌈1 / ε⌉₊ n D (d + 1) * repSharp ⌈1 / ε⌉₊ n D (d + 1) + 1)
        = (repSharp ⌈1 / ε⌉₊ n D (d + 1) * repSharp ⌈1 / ε⌉₊ n D (d + 1) + 1)
            * LGsharp ⌈1 / ε⌉₊ n D
          + 3 * (repSharp ⌈1 / ε⌉₊ n D (d + 1) * repSharp ⌈1 / ε⌉₊ n D (d + 1) + 1) := by
      ring
    omega
  -- 2^d·(R²+1) is flat across levels.
  have hkey : 2 ^ d * (repSharp ⌈1 / ε⌉₊ n D (d + 1) * repSharp ⌈1 / ε⌉₊ n D (d + 1) + 1)
      ≤ 4901 * ⌈1 / ε⌉₊ * ⌈1 / ε⌉₊ * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2))
        * (n + 3 * 2 ^ D + 4) ^ 2 := by
    have hR35 : repSharp ⌈1 / ε⌉₊ n D (d + 1)
        ≤ 35 * ⌈1 / ε⌉₊ * (2 ^ ((d + 1 + 1) / 2) * 2 ^ ((D + 1) / 2))
          * (n / 2 ^ (d + 1) + 3) := by
      unfold repSharp
      have hone : 1 ≤ ⌈1 / ε⌉₊ * (2 ^ ((d + 1 + 1) / 2) * 2 ^ ((D + 1) / 2))
          * (n / 2 ^ (d + 1) + 3) := by
        have h0 : (0:ℕ) < ⌈1 / ε⌉₊ * (2 ^ ((d + 1 + 1) / 2) * 2 ^ ((D + 1) / 2))
            * (n / 2 ^ (d + 1) + 3) := by positivity
        omega
      have e1 : 35 * ⌈1 / ε⌉₊ * (2 ^ ((d + 1 + 1) / 2) * 2 ^ ((D + 1) / 2))
          * (n / 2 ^ (d + 1) + 3)
          = 34 * (⌈1 / ε⌉₊ * (2 ^ ((d + 1 + 1) / 2) * 2 ^ ((D + 1) / 2))
              * (n / 2 ^ (d + 1) + 3))
            + ⌈1 / ε⌉₊ * (2 ^ ((d + 1 + 1) / 2) * 2 ^ ((D + 1) / 2))
              * (n / 2 ^ (d + 1) + 3) := by ring
      have e2 : 34 * ⌈1 / ε⌉₊ * (2 ^ ((d + 1 + 1) / 2) * 2 ^ ((D + 1) / 2))
          * (n / 2 ^ (d + 1) + 3)
          = 34 * (⌈1 / ε⌉₊ * (2 ^ ((d + 1 + 1) / 2) * 2 ^ ((D + 1) / 2))
              * (n / 2 ^ (d + 1) + 3)) := by ring
      omega
    -- (2^{(d+2)/2})² ≤ 2^{d+2}; regroup so the 2^d cancels into the level count.
    have hsq : 2 ^ d * (repSharp ⌈1 / ε⌉₊ n D (d + 1) * repSharp ⌈1 / ε⌉₊ n D (d + 1))
        ≤ 4900 * ⌈1 / ε⌉₊ * ⌈1 / ε⌉₊ * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2))
          * (n + 3 * 2 ^ D + 4) ^ 2 := by
      have h1 := Nat.mul_le_mul hR35 hR35
      have hp22 : (2:ℕ) ^ ((d + 1 + 1) / 2) * 2 ^ ((d + 1 + 1) / 2) ≤ 2 ^ (d + 2) := by
        rw [← Nat.pow_add]
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      -- 2^d · (2^{(d+2)/2})² · (n/2^{d+1}+3)² ≤ 4·(2^d·(n/2^{d+1}+3))² and
      -- 2^d·(n/2^{d+1}+3) ≤ n + 3·2^D + 4.
      have hlin : 2 ^ d * (n / 2 ^ (d + 1) + 3) ≤ n + 3 * 2 ^ D + 4 := by
        have hdm : n / 2 ^ (d + 1) * 2 ^ (d + 1) ≤ n := Nat.div_mul_le_self _ _
        have hpow : (2:ℕ) ^ (d + 1) = 2 ^ d * 2 := Nat.pow_succ 2 d
        have h2D : (2:ℕ) ^ d ≤ 2 ^ D := Nat.pow_le_pow_right (by norm_num) (by omega)
        nlinarith [Nat.zero_le (n / 2 ^ (d + 1))]
      calc 2 ^ d * (repSharp ⌈1 / ε⌉₊ n D (d + 1) * repSharp ⌈1 / ε⌉₊ n D (d + 1))
          ≤ 2 ^ d * ((35 * ⌈1 / ε⌉₊ * (2 ^ ((d + 1 + 1) / 2) * 2 ^ ((D + 1) / 2))
              * (n / 2 ^ (d + 1) + 3))
            * (35 * ⌈1 / ε⌉₊ * (2 ^ ((d + 1 + 1) / 2) * 2 ^ ((D + 1) / 2))
              * (n / 2 ^ (d + 1) + 3))) := Nat.mul_le_mul_left _ h1
        _ = 1225 * ⌈1 / ε⌉₊ * ⌈1 / ε⌉₊ * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2))
            * ((2 ^ ((d + 1 + 1) / 2) * 2 ^ ((d + 1 + 1) / 2))
              * (2 ^ d * ((n / 2 ^ (d + 1) + 3) * (n / 2 ^ (d + 1) + 3)))) := by
            ring
        _ ≤ 1225 * ⌈1 / ε⌉₊ * ⌈1 / ε⌉₊ * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2))
            * (2 ^ (d + 2) * (2 ^ d * ((n / 2 ^ (d + 1) + 3) * (n / 2 ^ (d + 1) + 3)))) := by
            refine Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hp22)
        _ = 4900 * ⌈1 / ε⌉₊ * ⌈1 / ε⌉₊ * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2))
            * ((2 ^ d * (n / 2 ^ (d + 1) + 3)) * (2 ^ d * (n / 2 ^ (d + 1) + 3))) := by
            rw [show (2:ℕ) ^ (d + 2) = 2 ^ d * 4 by rw [Nat.pow_add]]
            ring
        _ ≤ 4900 * ⌈1 / ε⌉₊ * ⌈1 / ε⌉₊ * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2))
            * ((n + 3 * 2 ^ D + 4) * (n + 3 * 2 ^ D + 4)) := by
            exact Nat.mul_le_mul_left _ (Nat.mul_le_mul hlin hlin)
        _ = 4900 * ⌈1 / ε⌉₊ * ⌈1 / ε⌉₊ * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2))
            * (n + 3 * 2 ^ D + 4) ^ 2 := by
            ring
    have h2d : 2 ^ d ≤ ⌈1 / ε⌉₊ * ⌈1 / ε⌉₊ * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2))
        * (n + 3 * 2 ^ D + 4) ^ 2 := by
      have h1 : (2:ℕ) ^ d ≤ 2 ^ D := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : (2:ℕ) ^ D ≤ 2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2) := by
        rw [← Nat.pow_add]
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      have h3 : 1 ≤ (n + 3 * 2 ^ D + 4) ^ 2 := Nat.one_le_pow _ _ (by omega)
      have h4 : ⌈1 / ε⌉₊ * ⌈1 / ε⌉₊ * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2))
          * (n + 3 * 2 ^ D + 4) ^ 2
          ≥ 1 * 1 * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2)) * 1 :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hE hE) le_rfl) h3
      have h5 : 1 * 1 * ((2:ℕ) ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2)) * 1
          = 2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2) := by ring
      omega
    have e1 : 2 ^ d * (repSharp ⌈1 / ε⌉₊ n D (d + 1) * repSharp ⌈1 / ε⌉₊ n D (d + 1) + 1)
        = 2 ^ d * (repSharp ⌈1 / ε⌉₊ n D (d + 1) * repSharp ⌈1 / ε⌉₊ n D (d + 1))
          + 2 ^ d := by ring
    have e2 : 4901 * ⌈1 / ε⌉₊ * ⌈1 / ε⌉₊ * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2))
        * (n + 3 * 2 ^ D + 4) ^ 2
        = 4900 * ⌈1 / ε⌉₊ * ⌈1 / ε⌉₊ * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2))
          * (n + 3 * 2 ^ D + 4) ^ 2
          + ⌈1 / ε⌉₊ * ⌈1 / ε⌉₊ * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2))
          * (n + 3 * 2 ^ D + 4) ^ 2 := by ring
    omega
  -- The bump term times 2^d is also flat.
  have hbump2 : 2 ^ d * (34 * ⌈1 / ε⌉₊ * (2 ^ ((d + 1) / 2) * 2 ^ ((D + 1) / 2))
      * (n / 2 ^ d + 2))
      ≤ 34 * ⌈1 / ε⌉₊ * ⌈1 / ε⌉₊ * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2))
        * (n + 3 * 2 ^ D + 4) ^ 2 := by
    have hp1 : (2:ℕ) ^ ((d + 1) / 2) ≤ 2 ^ ((D + 1) / 2) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hlin2 : 2 ^ d * (n / 2 ^ d + 2) ≤ n + 3 * 2 ^ D + 4 := by
      have hdm : n / 2 ^ d * 2 ^ d ≤ n := Nat.div_mul_le_self _ _
      have h2D : (2:ℕ) ^ d ≤ 2 ^ D := Nat.pow_le_pow_right (by norm_num) (by omega)
      have e : 2 ^ d * (n / 2 ^ d + 2) = n / 2 ^ d * 2 ^ d + 2 * 2 ^ d := by ring
      omega
    have hsq2 : n + 3 * 2 ^ D + 4 ≤ (n + 3 * 2 ^ D + 4) ^ 2 :=
      Nat.le_self_pow (by omega) _
    calc 2 ^ d * (34 * ⌈1 / ε⌉₊ * (2 ^ ((d + 1) / 2) * 2 ^ ((D + 1) / 2))
        * (n / 2 ^ d + 2))
        = 34 * ⌈1 / ε⌉₊ * (2 ^ ((d + 1) / 2) * 2 ^ ((D + 1) / 2))
          * (2 ^ d * (n / 2 ^ d + 2)) := by ring
      _ ≤ 34 * ⌈1 / ε⌉₊ * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2))
          * (2 ^ d * (n / 2 ^ d + 2)) := by
          refine Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ ?_)
          exact Nat.mul_le_mul_right _ hp1
      _ ≤ 34 * ⌈1 / ε⌉₊ * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2))
          * (n + 3 * 2 ^ D + 4) := Nat.mul_le_mul_left _ hlin2
      _ ≤ 34 * ⌈1 / ε⌉₊ * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2))
          * (n + 3 * 2 ^ D + 4) ^ 2 := Nat.mul_le_mul_left _ hsq2
      _ ≤ 34 * ⌈1 / ε⌉₊ * ⌈1 / ε⌉₊ * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2))
          * (n + 3 * 2 ^ D + 4) ^ 2 := by
          have e : 34 * ⌈1 / ε⌉₊ * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2))
              * (n + 3 * 2 ^ D + 4) ^ 2
              = 34 * ⌈1 / ε⌉₊ * 1 * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2))
              * (n + 3 * 2 ^ D + 4) ^ 2 := by ring
          rw [e]
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
            (Nat.mul_le_mul_left _ hE))
  -- Assemble into FLAT.
  have hmul := Nat.mul_le_mul_left (2 ^ d) hnode
  have hdist : 2 ^ d * ((LGsharp ⌈1 / ε⌉₊ n D + 3)
      * (repSharp ⌈1 / ε⌉₊ n D (d + 1) * repSharp ⌈1 / ε⌉₊ n D (d + 1) + 1)
      + 34 * ⌈1 / ε⌉₊ * (2 ^ ((d + 1) / 2) * 2 ^ ((D + 1) / 2)) * (n / 2 ^ d + 2))
      = (LGsharp ⌈1 / ε⌉₊ n D + 3)
        * (2 ^ d * (repSharp ⌈1 / ε⌉₊ n D (d + 1) * repSharp ⌈1 / ε⌉₊ n D (d + 1) + 1))
        + 2 ^ d * (34 * ⌈1 / ε⌉₊ * (2 ^ ((d + 1) / 2) * 2 ^ ((D + 1) / 2))
          * (n / 2 ^ d + 2)) := by ring
  have hLGmul := Nat.mul_le_mul_left (LGsharp ⌈1 / ε⌉₊ n D + 3) hkey
  have hflat : FLAT ⌈1 / ε⌉₊ n D (LGsharp ⌈1 / ε⌉₊ n D)
      = (LGsharp ⌈1 / ε⌉₊ n D + 3) * (4901 * ⌈1 / ε⌉₊ * ⌈1 / ε⌉₊
          * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2)) * (n + 3 * 2 ^ D + 4) ^ 2)
        + (LGsharp ⌈1 / ε⌉₊ n D + 3) * (99 * ⌈1 / ε⌉₊ * ⌈1 / ε⌉₊
          * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2)) * (n + 3 * 2 ^ D + 4) ^ 2) := by
    unfold FLAT
    ring
  have hb3 : 2 ^ d * (34 * ⌈1 / ε⌉₊ * (2 ^ ((d + 1) / 2) * 2 ^ ((D + 1) / 2))
      * (n / 2 ^ d + 2))
      ≤ (LGsharp ⌈1 / ε⌉₊ n D + 3) * (99 * ⌈1 / ε⌉₊ * ⌈1 / ε⌉₊
        * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2)) * (n + 3 * 2 ^ D + 4) ^ 2) := by
    have h1 : 34 * ⌈1 / ε⌉₊ * ⌈1 / ε⌉₊ * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2))
        * (n + 3 * 2 ^ D + 4) ^ 2
        ≤ (LGsharp ⌈1 / ε⌉₊ n D + 3) * (99 * ⌈1 / ε⌉₊ * ⌈1 / ε⌉₊
          * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2)) * (n + 3 * 2 ^ D + 4) ^ 2) := by
      have h2 : 34 * ⌈1 / ε⌉₊ * ⌈1 / ε⌉₊ * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2))
          * (n + 3 * 2 ^ D + 4) ^ 2
          = 34 * (⌈1 / ε⌉₊ * ⌈1 / ε⌉₊ * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2))
            * (n + 3 * 2 ^ D + 4) ^ 2) := by ring
      have h3 : (LGsharp ⌈1 / ε⌉₊ n D + 3) * (99 * ⌈1 / ε⌉₊ * ⌈1 / ε⌉₊
          * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2)) * (n + 3 * 2 ^ D + 4) ^ 2)
          = ((LGsharp ⌈1 / ε⌉₊ n D + 3) * 99)
            * (⌈1 / ε⌉₊ * ⌈1 / ε⌉₊ * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2))
              * (n + 3 * 2 ^ D + 4) ^ 2) := by ring
      have h4 : 34 ≤ (LGsharp ⌈1 / ε⌉₊ n D + 3) * 99 := by omega
      have h5 := Nat.mul_le_mul_right
        (⌈1 / ε⌉₊ * ⌈1 / ε⌉₊ * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2))
          * (n + 3 * 2 ^ D + 4) ^ 2) h4
      omega
    exact le_trans hbump2 h1
  calc 2 ^ d * (convCost A B + sparsifyCost (deltaSharp ε D d) (conv A B))
      ≤ 2 ^ d * ((LGsharp ⌈1 / ε⌉₊ n D + 3)
          * (repSharp ⌈1 / ε⌉₊ n D (d + 1) * repSharp ⌈1 / ε⌉₊ n D (d + 1) + 1)
        + 34 * ⌈1 / ε⌉₊ * (2 ^ ((d + 1) / 2) * 2 ^ ((D + 1) / 2)) * (n / 2 ^ d + 2)) :=
        hmul
    _ = (LGsharp ⌈1 / ε⌉₊ n D + 3)
          * (2 ^ d * (repSharp ⌈1 / ε⌉₊ n D (d + 1) * repSharp ⌈1 / ε⌉₊ n D (d + 1) + 1))
        + 2 ^ d * (34 * ⌈1 / ε⌉₊ * (2 ^ ((d + 1) / 2) * 2 ^ ((D + 1) / 2))
          * (n / 2 ^ d + 2)) := hdist
    _ ≤ (LGsharp ⌈1 / ε⌉₊ n D + 3) * (4901 * ⌈1 / ε⌉₊ * ⌈1 / ε⌉₊
          * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2)) * (n + 3 * 2 ^ D + 4) ^ 2)
        + (LGsharp ⌈1 / ε⌉₊ n D + 3) * (99 * ⌈1 / ε⌉₊ * ⌈1 / ε⌉₊
          * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2)) * (n + 3 * 2 ^ D + 4) ^ 2) := by
        omega
    _ = FLAT ⌈1 / ε⌉₊ n D (LGsharp ⌈1 / ε⌉₊ n D) := hflat.symm

/-! ## The tree roll-up -/

set_option maxHeartbeats 1000000 in
/-- **The multiplied-form tree recurrence**: a depth-`d` subtree's cost times
`2^d` is at most `(D-d)` flat levels plus the bottom line. -/
theorem dcSharpGoCost_le {ε : ℚ} (hε0 : 0 < ε) (n D : ℕ) :
    ∀ (S : List ℕ) (d : ℕ), d ≤ D → (S.length - 1) * 2 ^ d ≤ n →
    dcSharpGoCost ε D S d * 2 ^ d
      ≤ (D - d) * FLAT ⌈1 / ε⌉₊ n D (LGsharp ⌈1 / ε⌉₊ n D)
        + 2 ^ D * BOTC ⌈1 / ε⌉₊ n D (LGsharp ⌈1 / ε⌉₊ n D) := by
  intro S d hdD hs
  rw [dcSharpGoCost.eq_def]
  by_cases htriv : S.length ≤ 1
  · rw [if_pos htriv]
    have h32 := halmanCost_triv htriv (deltaBot ε D)
    have hBOTC : 64 ≤ BOTC ⌈1 / ε⌉₊ n D (LGsharp ⌈1 / ε⌉₊ n D) := by
      unfold BOTC
      omega
    have h2dD : (2:ℕ) ^ d ≤ 2 ^ D := Nat.pow_le_pow_right (by norm_num) hdD
    have hmul : 2 ^ D * 64 ≤ 2 ^ D * BOTC ⌈1 / ε⌉₊ n D (LGsharp ⌈1 / ε⌉₊ n D) :=
      Nat.mul_le_mul_left _ hBOTC
    have hc : halmanCost S (deltaBot ε D) * 2 ^ d ≤ 32 * 2 ^ D :=
      Nat.mul_le_mul h32 h2dD
    omega
  · rw [if_neg htriv]
    by_cases hDd : D ≤ d
    · rw [if_pos hDd]
      obtain rfl : D = d := by omega
      have h2d1 : 1 ≤ 2 ^ D := Nat.one_le_two_pow
      have hσ : S.length ≤ n / 2 ^ D + 1 := by
        have hdiv := (Nat.le_div_iff_mul_le (k := 2 ^ D) (by positivity)).mpr hs
        omega
      have hbc := bottomCost_le hε0 n D S hσ (by omega)
      have hmul := Nat.mul_le_mul_right (2 ^ D) hbc
      have e1 : BOTC ⌈1 / ε⌉₊ n D (LGsharp ⌈1 / ε⌉₊ n D) * 2 ^ D
          = 2 ^ D * BOTC ⌈1 / ε⌉₊ n D (LGsharp ⌈1 / ε⌉₊ n D) := by ring
      omega
    · rw [if_neg hDd]
      have hd : d < D := by omega
      have hslen : 2 ≤ S.length := by omega
      have hta : (S.take (S.length / 2)).length = S.length / 2 := by
        rw [List.length_take]
        omega
      have htb : (S.drop (S.length / 2)).length = S.length - S.length / 2 := by
        rw [List.length_drop]
      have hsA : ((S.take (S.length / 2)).length - 1) * 2 ^ (d + 1) ≤ n := by
        rw [hta, Nat.pow_succ]
        have e : (S.length / 2 - 1) * (2 ^ d * 2) = (2 * (S.length / 2 - 1)) * 2 ^ d := by
          ring
        rw [e]
        have h1 : 2 * (S.length / 2 - 1) ≤ S.length - 1 := by omega
        have h2 := Nat.mul_le_mul_right (2 ^ d) h1
        omega
      have hsB : ((S.drop (S.length / 2)).length - 1) * 2 ^ (d + 1) ≤ n := by
        rw [htb, Nat.pow_succ]
        have e : (S.length - S.length / 2 - 1) * (2 ^ d * 2)
            = (2 * (S.length - S.length / 2 - 1)) * 2 ^ d := by
          ring
        rw [e]
        have h1 : 2 * (S.length - S.length / 2 - 1) ≤ S.length - 1 := by omega
        have h2 := Nat.mul_le_mul_right (2 ^ d) h1
        omega
      have hcA := dcSharpGoCost_le hε0 n D (S.take (S.length / 2)) (d + 1)
        (by omega) hsA
      have hcB := dcSharpGoCost_le hε0 n D (S.drop (S.length / 2)) (d + 1)
        (by omega) hsB
      have hlA := dcSharpGo_length hε0 n D (S.take (S.length / 2)) (d + 1)
        (by omega) hsA
      have hlB := dcSharpGo_length hε0 n D (S.drop (S.length / 2)) (d + 1)
        (by omega) hsB
      set A := dcSharpGo ε D (S.take (S.length / 2)) (d + 1) with hAdef
      set B := dcSharpGo ε D (S.drop (S.length / 2)) (d + 1) with hBdef
      have hsn : S.length ≤ n / 2 ^ d + 1 := by
        have hdiv := (Nat.le_div_iff_mul_le (k := 2 ^ d) (by positivity)).mpr hs
        omega
      have hmassconv : massOf (conv A B) ≤ 2 ^ S.length := by
        rw [massOf_conv]
        calc massOf A * massOf B
            ≤ 2 ^ (S.take (S.length / 2)).length * 2 ^ (S.drop (S.length / 2)).length :=
              Nat.mul_le_mul (massOf_dcSharpGo ε D _ _) (massOf_dcSharpGo ε D _ _)
          _ = 2 ^ S.length := by
              rw [← pow_add, List.length_take, List.length_drop]
              congr 1
              omega
      have hbump : bumpSteps (deltaSharp ε D d) 1 (massOf (conv A B))
          ≤ 34 * ⌈1 / ε⌉₊ * (2 ^ ((d + 1) / 2) * 2 ^ ((D + 1) / 2)) * (n / 2 ^ d + 2) := by
        have h1 := bumpSteps_le (deltaSharp ε D d) (deltaSharp_pos hε0 D d)
          (massOf (conv A B))
        have hlog : Nat.log 2 (massOf (conv A B)) ≤ S.length := by
          calc Nat.log 2 (massOf (conv A B)) ≤ Nat.log 2 (2 ^ S.length) :=
                Nat.log_mono_right hmassconv
            _ = S.length := Nat.log_pow (b := 2) (by norm_num) _
        have hds := doubleSteps_deltaSharp hε0 D d
        calc bumpSteps (deltaSharp ε D d) 1 (massOf (conv A B))
            ≤ doubleSteps (deltaSharp ε D d) * (Nat.log 2 (massOf (conv A B)) + 1) := h1
          _ ≤ 34 * ⌈1 / ε⌉₊ * (2 ^ ((d + 1) / 2) * 2 ^ ((D + 1) / 2))
              * (n / 2 ^ d + 2) := Nat.mul_le_mul hds (by omega)
      have hnode := internal_node_flat hε0 n D d A B hd hlA hlB hbump
      -- Assemble.
      have hpow : (2:ℕ) ^ (d + 1) = 2 ^ d * 2 := Nat.pow_succ 2 d
      have hdist : (D - d) * FLAT ⌈1 / ε⌉₊ n D (LGsharp ⌈1 / ε⌉₊ n D)
          = (D - (d + 1)) * FLAT ⌈1 / ε⌉₊ n D (LGsharp ⌈1 / ε⌉₊ n D)
            + FLAT ⌈1 / ε⌉₊ n D (LGsharp ⌈1 / ε⌉₊ n D) := by
        have e : D - d = (D - (d + 1)) + 1 := by omega
        rw [e, Nat.succ_mul]
      have eA : dcSharpGoCost ε D (S.take (S.length / 2)) (d + 1) * 2 ^ (d + 1)
          = dcSharpGoCost ε D (S.take (S.length / 2)) (d + 1) * 2 ^ d * 2 := by
        rw [hpow]
        ring
      have eB : dcSharpGoCost ε D (S.drop (S.length / 2)) (d + 1) * 2 ^ (d + 1)
          = dcSharpGoCost ε D (S.drop (S.length / 2)) (d + 1) * 2 ^ d * 2 := by
        rw [hpow]
        ring
      rw [eA] at hcA
      rw [eB] at hcB
      have egoal : (dcSharpGoCost ε D (S.take (S.length / 2)) (d + 1)
          + dcSharpGoCost ε D (S.drop (S.length / 2)) (d + 1)
          + convCost A B + sparsifyCost (deltaSharp ε D d) (conv A B)) * 2 ^ d
          = dcSharpGoCost ε D (S.take (S.length / 2)) (d + 1) * 2 ^ d
            + dcSharpGoCost ε D (S.drop (S.length / 2)) (d + 1) * 2 ^ d
            + 2 ^ d * (convCost A B + sparsifyCost (deltaSharp ε D d) (conv A B)) := by
        ring
      omega

/-! ## The final collapse to the n^2.5 form -/

set_option maxHeartbeats 1600000 in
/-- Pure-arithmetic final collapse. Writing `SB = E·(√(nE)+1) + E²`, the tree
budget collapses to `Õ((n+2)²·SB)`, i.e. `Õ(n^2.5 ε^-1.5 + n² ε^-2)`. -/
theorem final_collapse (n E D : ℕ) (hE : 1 ≤ E)
    (hD_up : 2 ^ D ≤ Nat.sqrt (n / E) + 1)
    (hD_lo : Nat.sqrt (n / E) + 1 < 2 ^ (D + 1))
    (cost query : ℕ)
    (hcost : cost ≤ D * FLAT E n D (LGsharp E n D)
      + 2 ^ D * BOTC E n D (LGsharp E n D))
    (hquery : query ≤ repSharp E n D 0 + 1) :
    cost + query ≤ 10 ^ 7 * LGsharp E n D ^ 2 * (n + 2) ^ 2
      * (E * (Nat.sqrt (n * E) + 1) + E ^ 2) := by
  have hLG40 : 40 ≤ LGsharp E n D := by
    unfold LGsharp
    omega
  have hDle : D ≤ LGsharp E n D := by
    unfold LGsharp
    omega
  have hsqmono : Nat.sqrt (n / E) ≤ Nat.sqrt n := Nat.sqrt_le_sqrt (Nat.div_le_self _ _)
  have hsqn : Nat.sqrt n ≤ n := Nat.sqrt_le_self n
  have h2Dn : 2 ^ D ≤ n + 1 := by omega
  have hSB1 : 1 ≤ E * (Nat.sqrt (n * E) + 1) + E ^ 2 := by
    have h1 : 1 * 1 ≤ E * (Nat.sqrt (n * E) + 1) := Nat.mul_le_mul hE (by omega)
    omega
  -- E·√(n/E) ≤ √(nE).
  have hEs : E * Nat.sqrt (n / E) ≤ Nat.sqrt (n * E) := by
    refine Nat.le_sqrt.mpr ?_
    have h1 : Nat.sqrt (n / E) * Nat.sqrt (n / E) ≤ n / E := Nat.sqrt_le _
    have h2 : n / E * E ≤ n := Nat.div_mul_le_self _ _
    calc E * Nat.sqrt (n / E) * (E * Nat.sqrt (n / E))
        = E * E * (Nat.sqrt (n / E) * Nat.sqrt (n / E)) := by ring
      _ ≤ E * E * (n / E) := Nat.mul_le_mul_left _ h1
      _ = E * (n / E * E) := by ring
      _ ≤ E * n := Nat.mul_le_mul_left _ h2
      _ = n * E := by ring
  -- n/2^D ≤ 2√(nE) + 2E.
  have hnbound : n ≤ (2 * Nat.sqrt (n * E) + 2 * E) * 2 ^ D := by
    have h1 : n / E < (Nat.sqrt (n / E) + 1) * (Nat.sqrt (n / E) + 1) :=
      Nat.lt_succ_sqrt _
    have h2 : E * (n / E) + n % E = n := Nat.div_add_mod n E
    have h3 : n % E < E := Nat.mod_lt _ (by omega)
    have h4 : n < E * ((Nat.sqrt (n / E) + 1) * (Nat.sqrt (n / E) + 1)) := by
      have h5 : n / E + 1 ≤ (Nat.sqrt (n / E) + 1) * (Nat.sqrt (n / E) + 1) := by
        omega
      have h6 := Nat.mul_le_mul_left E h5
      have e : E * (n / E + 1) = E * (n / E) + E := by ring
      omega
    have h5 : E * (Nat.sqrt (n / E) + 1) ≤ Nat.sqrt (n * E) + E := by
      have e : E * (Nat.sqrt (n / E) + 1) = E * Nat.sqrt (n / E) + E := by ring
      omega
    have h6 : Nat.sqrt (n / E) + 1 ≤ 2 * 2 ^ D := by
      have e : (2:ℕ) ^ (D + 1) = 2 ^ D * 2 := Nat.pow_succ 2 D
      omega
    calc n ≤ E * ((Nat.sqrt (n / E) + 1) * (Nat.sqrt (n / E) + 1)) := by omega
      _ = (E * (Nat.sqrt (n / E) + 1)) * (Nat.sqrt (n / E) + 1) := by ring
      _ ≤ (Nat.sqrt (n * E) + E) * (2 * 2 ^ D) := Nat.mul_le_mul h5 h6
      _ = (2 * Nat.sqrt (n * E) + 2 * E) * 2 ^ D := by ring
  have hnD : n / 2 ^ D ≤ 2 * Nat.sqrt (n * E) + 2 * E := by
    have h1 : (0:ℕ) < 2 ^ D := by positivity
    have h2 := Nat.div_le_div_right (c := 2 ^ D) hnbound
    rw [Nat.mul_div_cancel _ h1] at h2
    exact h2
  -- Common conversions.
  have hE2s : E * E * (Nat.sqrt (n / E) + 1)
      ≤ E * (Nat.sqrt (n * E) + 1) + E ^ 2 := by
    have e1 : E * E * (Nat.sqrt (n / E) + 1) = E * (E * Nat.sqrt (n / E)) + E * E := by
      ring
    have h1 := Nat.mul_le_mul_left E hEs
    have e2 : E ^ 2 = E * E := by ring
    have e3 : E * (Nat.sqrt (n * E) + 1) = E * Nat.sqrt (n * E) + E := by ring
    omega
  have hPP : (2:ℕ) ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2) ≤ 2 * (Nat.sqrt (n / E) + 1) := by
    have h1 : (2:ℕ) ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2) ≤ 2 ^ (D + 1) := by
      rw [← Nat.pow_add]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have e : (2:ℕ) ^ (D + 1) = 2 ^ D * 2 := Nat.pow_succ 2 D
    omega
  have hnpart : (n + 3 * 2 ^ D + 4) ^ 2 ≤ 16 * (n + 2) ^ 2 := by
    have h1 : n + 3 * 2 ^ D + 4 ≤ 4 * (n + 2) := by omega
    calc (n + 3 * 2 ^ D + 4) ^ 2 ≤ (4 * (n + 2)) ^ 2 := Nat.pow_le_pow_left h1 2
      _ = 16 * (n + 2) ^ 2 := by ring
  -- (a) The flat part.
  have hFLAT : FLAT E n D (LGsharp E n D)
      ≤ 320000 * LGsharp E n D * ((n + 2) ^ 2
          * (E * (Nat.sqrt (n * E) + 1) + E ^ 2)) := by
    unfold FLAT
    have step1 : 5000 * (LGsharp E n D + 3) * E * E
        * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2)) * (n + 3 * 2 ^ D + 4) ^ 2
        ≤ 5000 * (LGsharp E n D + 3) * E * E
          * (2 * (Nat.sqrt (n / E) + 1)) * (16 * (n + 2) ^ 2) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ hPP) hnpart
    have e1 : 5000 * (LGsharp E n D + 3) * E * E
        * (2 * (Nat.sqrt (n / E) + 1)) * (16 * (n + 2) ^ 2)
        = 160000 * (LGsharp E n D + 3)
          * ((n + 2) ^ 2 * (E * E * (Nat.sqrt (n / E) + 1))) := by
      ring
    have step2 : 160000 * (LGsharp E n D + 3)
        * ((n + 2) ^ 2 * (E * E * (Nat.sqrt (n / E) + 1)))
        ≤ 160000 * (LGsharp E n D + 3)
          * ((n + 2) ^ 2 * (E * (Nat.sqrt (n * E) + 1) + E ^ 2)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hE2s)
    have step3 : 160000 * (LGsharp E n D + 3)
        * ((n + 2) ^ 2 * (E * (Nat.sqrt (n * E) + 1) + E ^ 2))
        ≤ 320000 * LGsharp E n D
          * ((n + 2) ^ 2 * (E * (Nat.sqrt (n * E) + 1) + E ^ 2)) := by
      refine Nat.mul_le_mul_right _ ?_
      omega
    omega
  have hDFLAT : D * FLAT E n D (LGsharp E n D)
      ≤ 320000 * LGsharp E n D ^ 2
          * ((n + 2) ^ 2 * (E * (Nat.sqrt (n * E) + 1) + E ^ 2)) := by
    calc D * FLAT E n D (LGsharp E n D)
        ≤ LGsharp E n D * (320000 * LGsharp E n D * ((n + 2) ^ 2
            * (E * (Nat.sqrt (n * E) + 1) + E ^ 2))) :=
          Nat.mul_le_mul hDle hFLAT
      _ = 320000 * LGsharp E n D ^ 2
            * ((n + 2) ^ 2 * (E * (Nat.sqrt (n * E) + 1) + E ^ 2)) := by
          ring
  -- (b) The bottom part.
  have hBOT : 2 ^ D * BOTC E n D (LGsharp E n D)
      ≤ 40300 * LGsharp E n D
          * ((n + 2) ^ 2 * (E * (Nat.sqrt (n * E) + 1) + E ^ 2)) := by
    unfold BOTC
    have ha : n / 2 ^ D * 2 ^ D ≤ n := Nat.div_mul_le_self _ _
    have hcube : 2 ^ D * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2))
        * (n / 2 ^ D + 3) ^ 3
        ≤ 2 * ((n + 2) ^ 2 * (2 * Nat.sqrt (n * E) + 2 * E + 63)) := by
      have hPP2 : (2:ℕ) ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2) ≤ 2 ^ D * 2 := by
        have h1 : (2:ℕ) ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2) ≤ 2 ^ (D + 1) := by
          rw [← Nat.pow_add]
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
        have e : (2:ℕ) ^ (D + 1) = 2 ^ D * 2 := Nat.pow_succ 2 D
        omega
      have hstep : 2 ^ D * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2))
          * (n / 2 ^ D + 3) ^ 3
          ≤ 2 * (2 ^ D * 2 ^ D * (n / 2 ^ D + 3) ^ 3) := by
        have h1 := Nat.mul_le_mul_right ((n / 2 ^ D + 3) ^ 3)
          (Nat.mul_le_mul_left (2 ^ D) hPP2)
        have e : 2 ^ D * (2 ^ D * 2) * (n / 2 ^ D + 3) ^ 3
            = 2 * (2 ^ D * 2 ^ D * (n / 2 ^ D + 3) ^ 3) := by ring
        omega
      have hexp : 2 ^ D * 2 ^ D * (n / 2 ^ D + 3) ^ 3
          ≤ (n + 2) ^ 2 * (2 * Nat.sqrt (n * E) + 2 * E + 63) := by
        have e1 : 2 ^ D * 2 ^ D * (n / 2 ^ D + 3) ^ 3
            = (n / 2 ^ D) * ((n / 2 ^ D * 2 ^ D) * (n / 2 ^ D * 2 ^ D))
              + 9 * ((n / 2 ^ D * 2 ^ D) * (n / 2 ^ D * 2 ^ D))
              + 27 * (2 ^ D * (n / 2 ^ D * 2 ^ D))
              + 27 * (2 ^ D * 2 ^ D) := by
          ring
        have b1 : (n / 2 ^ D) * ((n / 2 ^ D * 2 ^ D) * (n / 2 ^ D * 2 ^ D))
            ≤ (2 * Nat.sqrt (n * E) + 2 * E) * (n * n) :=
          Nat.mul_le_mul hnD (Nat.mul_le_mul ha ha)
        have b2 : 9 * ((n / 2 ^ D * 2 ^ D) * (n / 2 ^ D * 2 ^ D)) ≤ 9 * (n * n) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul ha ha)
        have b3 : 27 * (2 ^ D * (n / 2 ^ D * 2 ^ D)) ≤ 27 * ((n + 1) * n) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul h2Dn ha)
        have b4 : 27 * ((2:ℕ) ^ D * 2 ^ D) ≤ 27 * ((n + 1) * (n + 1)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul h2Dn h2Dn)
        have c1 : (2 * Nat.sqrt (n * E) + 2 * E) * (n * n)
            ≤ (n + 2) ^ 2 * (2 * Nat.sqrt (n * E) + 2 * E) := by
          have e : (n + 2) ^ 2 * (2 * Nat.sqrt (n * E) + 2 * E)
              = (2 * Nat.sqrt (n * E) + 2 * E) * ((n + 2) * (n + 2)) := by ring
          have h1 : n * n ≤ (n + 2) * (n + 2) := Nat.mul_le_mul (by omega) (by omega)
          have h2 := Nat.mul_le_mul_left (2 * Nat.sqrt (n * E) + 2 * E) h1
          omega
        have c2 : 9 * (n * n) + 27 * ((n + 1) * n) + 27 * ((n + 1) * (n + 1))
            ≤ 63 * ((n + 2) * (n + 2)) := by nlinarith
        have e2 : (n + 2) ^ 2 * (2 * Nat.sqrt (n * E) + 2 * E + 63)
            = (n + 2) ^ 2 * (2 * Nat.sqrt (n * E) + 2 * E) + 63 * ((n + 2) * (n + 2)) := by
          ring
        omega
      omega
    -- Multiply through by 300·LG·E and add the +64 tail.
    have hmul : 2 ^ D * (300 * LGsharp E n D * E
        * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2)) * (n / 2 ^ D + 3) ^ 3)
        ≤ 300 * LGsharp E n D * E
          * (2 * ((n + 2) ^ 2 * (2 * Nat.sqrt (n * E) + 2 * E + 63))) := by
      have e1 : 2 ^ D * (300 * LGsharp E n D * E
          * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2)) * (n / 2 ^ D + 3) ^ 3)
          = 300 * LGsharp E n D * E * (2 ^ D
            * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2)) * (n / 2 ^ D + 3) ^ 3) := by
        ring
      rw [e1]
      exact Nat.mul_le_mul_left _ hcube
    have hEconv : E * (2 * Nat.sqrt (n * E) + 2 * E + 63)
        ≤ 67 * (E * (Nat.sqrt (n * E) + 1) + E ^ 2) := by
      have e1 : E * (2 * Nat.sqrt (n * E) + 2 * E + 63)
          = 2 * (E * Nat.sqrt (n * E)) + 2 * (E * E) + 63 * E := by ring
      have e2 : E * (Nat.sqrt (n * E) + 1) = E * Nat.sqrt (n * E) + E := by ring
      have e3 : E ^ 2 = E * E := by ring
      have h1 : E ≤ E * Nat.sqrt (n * E) + E := by omega
      omega
    have hfin : 300 * LGsharp E n D * E
        * (2 * ((n + 2) ^ 2 * (2 * Nat.sqrt (n * E) + 2 * E + 63)))
        ≤ 40200 * LGsharp E n D
          * ((n + 2) ^ 2 * (E * (Nat.sqrt (n * E) + 1) + E ^ 2)) := by
      have e1 : 300 * LGsharp E n D * E
          * (2 * ((n + 2) ^ 2 * (2 * Nat.sqrt (n * E) + 2 * E + 63)))
          = 600 * LGsharp E n D * ((n + 2) ^ 2
            * (E * (2 * Nat.sqrt (n * E) + 2 * E + 63))) := by
        ring
      have h1 := Nat.mul_le_mul_left ((n + 2) ^ 2) hEconv
      have h2 := Nat.mul_le_mul_left (600 * LGsharp E n D) h1
      have e2 : 600 * LGsharp E n D * ((n + 2) ^ 2
          * (67 * (E * (Nat.sqrt (n * E) + 1) + E ^ 2)))
          = 40200 * LGsharp E n D * ((n + 2) ^ 2
            * (E * (Nat.sqrt (n * E) + 1) + E ^ 2)) := by
        ring
      omega
    have htail : 2 ^ D * 64 ≤ 100 * LGsharp E n D
        * ((n + 2) ^ 2 * (E * (Nat.sqrt (n * E) + 1) + E ^ 2)) := by
      have h1 : 2 ^ D * 64 ≤ (n + 1) * 64 := Nat.mul_le_mul_right _ h2Dn
      have h2 : (n + 1) * 64 ≤ 100 * ((n + 2) ^ 2 * 1) := by nlinarith
      have h3 : 100 * ((n + 2) ^ 2 * 1)
          ≤ 100 * ((n + 2) ^ 2 * (E * (Nat.sqrt (n * E) + 1) + E ^ 2)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hSB1)
      have h4 : 100 * ((n + 2) ^ 2 * (E * (Nat.sqrt (n * E) + 1) + E ^ 2))
          ≤ 100 * LGsharp E n D
            * ((n + 2) ^ 2 * (E * (Nat.sqrt (n * E) + 1) + E ^ 2)) := by
        have e : 100 * LGsharp E n D
            * ((n + 2) ^ 2 * (E * (Nat.sqrt (n * E) + 1) + E ^ 2))
            = 100 * ((n + 2) ^ 2 * (E * (Nat.sqrt (n * E) + 1) + E ^ 2))
              * LGsharp E n D := by ring
        have h5 := Nat.le_mul_of_pos_right
          (100 * ((n + 2) ^ 2 * (E * (Nat.sqrt (n * E) + 1) + E ^ 2)))
          (show 0 < LGsharp E n D by omega)
        omega
      omega
    have edist : 2 ^ D * (300 * LGsharp E n D * E
        * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2)) * (n / 2 ^ D + 3) ^ 3 + 64)
        = 2 ^ D * (300 * LGsharp E n D * E
          * (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2)) * (n / 2 ^ D + 3) ^ 3)
          + 2 ^ D * 64 := by ring
    have esum : 40300 * LGsharp E n D
        * ((n + 2) ^ 2 * (E * (Nat.sqrt (n * E) + 1) + E ^ 2))
        = 40200 * LGsharp E n D
          * ((n + 2) ^ 2 * (E * (Nat.sqrt (n * E) + 1) + E ^ 2))
          + 100 * LGsharp E n D
          * ((n + 2) ^ 2 * (E * (Nat.sqrt (n * E) + 1) + E ^ 2)) := by ring
    omega
  -- (c) The query.
  have hQ : repSharp E n D 0 + 1 ≤ 200 * ((n + 2) ^ 2
      * (E * (Nat.sqrt (n * E) + 1) + E ^ 2)) := by
    unfold repSharp
    have hp0 : (2:ℕ) ^ ((0 + 1) / 2) = 1 := by norm_num
    have hdd : n / 1 = n := Nat.div_one n
    rw [hp0, hdd]
    have h1 : (2:ℕ) ^ ((D + 1) / 2) ≤ 2 * (n + 2) := by
      have h2 : (2:ℕ) ^ ((D + 1) / 2) ≤ 2 ^ (D + 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have e : (2:ℕ) ^ (D + 1) = 2 ^ D * 2 := Nat.pow_succ 2 D
      omega
    have h3 : 1 * (2 ^ ((D + 1) / 2)) = (2:ℕ) ^ ((D + 1) / 2) := by ring
    have hstep : 34 * E * (1 * 2 ^ ((D + 1) / 2)) * (n + 3)
        ≤ 34 * E * (2 * (n + 2)) * (n + 3) := by
      refine Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ ?_)
      omega
    have e1 : 34 * E * (2 * (n + 2)) * (n + 3) ≤ 68 * (E * ((n + 2) * (n + 3))) := by
      have e : 34 * E * (2 * (n + 2)) * (n + 3) = 68 * (E * ((n + 2) * (n + 3))) := by
        ring
      omega
    have e2 : (n + 2) * (n + 3) ≤ 2 * (n + 2) ^ 2 := by nlinarith
    have h4 : 68 * (E * ((n + 2) * (n + 3))) ≤ 136 * (E * (n + 2) ^ 2) := by
      have h5 := Nat.mul_le_mul_left E e2
      have e : 136 * (E * (n + 2) ^ 2) = 68 * (E * (2 * (n + 2) ^ 2)) := by ring
      have h6 := Nat.mul_le_mul_left (68:ℕ) h5
      omega
    have h7 : 136 * (E * (n + 2) ^ 2) + 2
        ≤ 200 * ((n + 2) ^ 2 * (E * (Nat.sqrt (n * E) + 1) + E ^ 2)) := by
      have h8 : E ≤ E * (Nat.sqrt (n * E) + 1) + E ^ 2 := by
        have h9 : E * 1 ≤ E * (Nat.sqrt (n * E) + 1) :=
          Nat.mul_le_mul_left _ (by omega)
        omega
      have h10 : E * (n + 2) ^ 2 ≤ (n + 2) ^ 2
          * (E * (Nat.sqrt (n * E) + 1) + E ^ 2) := by
        have e : E * (n + 2) ^ 2 = (n + 2) ^ 2 * E := by ring
        have h11 := Nat.mul_le_mul_left ((n + 2) ^ 2) h8
        omega
      have h12 : 1 ≤ (n + 2) ^ 2 * (E * (Nat.sqrt (n * E) + 1) + E ^ 2) := by
        have h13 : 1 * 1 ≤ (n + 2) ^ 2 * (E * (Nat.sqrt (n * E) + 1) + E ^ 2) :=
          Nat.mul_le_mul (Nat.one_le_pow _ _ (by omega)) hSB1
        omega
      have h14 := Nat.mul_le_mul_left (136:ℕ) h10
      omega
    omega
  -- Total.
  have hfin : cost + query
      ≤ 320000 * LGsharp E n D ^ 2
          * ((n + 2) ^ 2 * (E * (Nat.sqrt (n * E) + 1) + E ^ 2))
        + 40300 * LGsharp E n D
          * ((n + 2) ^ 2 * (E * (Nat.sqrt (n * E) + 1) + E ^ 2))
        + 200 * ((n + 2) ^ 2 * (E * (Nat.sqrt (n * E) + 1) + E ^ 2)) := by
    omega
  have hLGsq : 40300 * LGsharp E n D
      * ((n + 2) ^ 2 * (E * (Nat.sqrt (n * E) + 1) + E ^ 2))
      + 200 * ((n + 2) ^ 2 * (E * (Nat.sqrt (n * E) + 1) + E ^ 2))
      ≤ 40500 * LGsharp E n D ^ 2
        * ((n + 2) ^ 2 * (E * (Nat.sqrt (n * E) + 1) + E ^ 2)) := by
    have h1 : LGsharp E n D ≤ LGsharp E n D ^ 2 := by
      have e : LGsharp E n D ^ 2 = LGsharp E n D * LGsharp E n D := by ring
      have h2 := Nat.le_mul_of_pos_right (LGsharp E n D) (show 0 < LGsharp E n D by omega)
      omega
    have h3 : 40300 * LGsharp E n D ≤ 40300 * LGsharp E n D ^ 2 :=
      Nat.mul_le_mul_left _ h1
    have h4 : 200 ≤ 200 * LGsharp E n D ^ 2 :=
      Nat.le_mul_of_pos_right _ (by positivity)
    have h5 := Nat.mul_le_mul_right
      ((n + 2) ^ 2 * (E * (Nat.sqrt (n * E) + 1) + E ^ 2)) h3
    have h6 := Nat.mul_le_mul_right
      ((n + 2) ^ 2 * (E * (Nat.sqrt (n * E) + 1) + E ^ 2)) h4
    have e1 : (40300 * LGsharp E n D ^ 2 + 200 * LGsharp E n D ^ 2)
        * ((n + 2) ^ 2 * (E * (Nat.sqrt (n * E) + 1) + E ^ 2))
        = 40500 * LGsharp E n D ^ 2
          * ((n + 2) ^ 2 * (E * (Nat.sqrt (n * E) + 1) + E ^ 2)) := by ring
    have e2 : 40300 * LGsharp E n D
        * ((n + 2) ^ 2 * (E * (Nat.sqrt (n * E) + 1) + E ^ 2))
        = (40300 * LGsharp E n D)
          * ((n + 2) ^ 2 * (E * (Nat.sqrt (n * E) + 1) + E ^ 2)) := by ring
    have e3 : (40300 * LGsharp E n D ^ 2)
        * ((n + 2) ^ 2 * (E * (Nat.sqrt (n * E) + 1) + E ^ 2))
        + (200 * LGsharp E n D ^ 2)
        * ((n + 2) ^ 2 * (E * (Nat.sqrt (n * E) + 1) + E ^ 2))
        = (40300 * LGsharp E n D ^ 2 + 200 * LGsharp E n D ^ 2)
          * ((n + 2) ^ 2 * (E * (Nat.sqrt (n * E) + 1) + E ^ 2)) := by ring
    omega
  have hfinal : 320000 * LGsharp E n D ^ 2
        * ((n + 2) ^ 2 * (E * (Nat.sqrt (n * E) + 1) + E ^ 2))
      + 40500 * LGsharp E n D ^ 2
        * ((n + 2) ^ 2 * (E * (Nat.sqrt (n * E) + 1) + E ^ 2))
      ≤ 10 ^ 7 * LGsharp E n D ^ 2 * (n + 2) ^ 2
        * (E * (Nat.sqrt (n * E) + 1) + E ^ 2) := by
    have e1 : 320000 * LGsharp E n D ^ 2
          * ((n + 2) ^ 2 * (E * (Nat.sqrt (n * E) + 1) + E ^ 2))
        + 40500 * LGsharp E n D ^ 2
          * ((n + 2) ^ 2 * (E * (Nat.sqrt (n * E) + 1) + E ^ 2))
        = 360500 * (LGsharp E n D ^ 2 * (n + 2) ^ 2
            * (E * (Nat.sqrt (n * E) + 1) + E ^ 2)) := by ring
    have e2 : 10 ^ 7 * LGsharp E n D ^ 2 * (n + 2) ^ 2
        * (E * (Nat.sqrt (n * E) + 1) + E ^ 2)
        = 10000000 * (LGsharp E n D ^ 2 * (n + 2) ^ 2
            * (E * (Nat.sqrt (n * E) + 1) + E ^ 2)) := by ring
    have h1 : (0:ℕ) < LGsharp E n D ^ 2 * (n + 2) ^ 2
        * (E * (Nat.sqrt (n * E) + 1) + E ^ 2) := by positivity
    omega
  omega

/-- **The sharp running-time theorem**: the sharp algorithm answers a
#Knapsack instance within

  `10⁷ · LOG² · (n+2)² · (⌈1/ε⌉·(√(n·⌈1/ε⌉)+1) + ⌈1/ε⌉²)`

operations - that is, `Õ(n^2.5·ε^-1.5 + n²·ε^-2)`, matching the best known
deterministic bound (GMW, ICALP 2018) term for term. -/
theorem approxCountSharpCost_le (S : List ℕ) (C : ℕ) (ε : ℚ)
    (h0 : 0 < ε) (_h1 : ε ≤ 1) :
    approxCountSharpCost S C ε
      ≤ 10 ^ 7
        * LGsharp ⌈1 / ε⌉₊ S.length (sharpDepth S.length ⌈1 / ε⌉₊) ^ 2
        * (S.length + 2) ^ 2
        * (⌈1 / ε⌉₊ * (Nat.sqrt (S.length * ⌈1 / ε⌉₊) + 1) + ⌈1 / ε⌉₊ ^ 2) := by
  have hE : 1 ≤ ⌈1 / ε⌉₊ := one_le_invE h0
  have hD_up : 2 ^ sharpDepth S.length ⌈1 / ε⌉₊
      ≤ Nat.sqrt (S.length / ⌈1 / ε⌉₊) + 1 := by
    unfold sharpDepth
    exact Nat.pow_log_le_self 2 (by omega)
  have hD_lo : Nat.sqrt (S.length / ⌈1 / ε⌉₊) + 1
      < 2 ^ (sharpDepth S.length ⌈1 / ε⌉₊ + 1) := by
    unfold sharpDepth
    exact Nat.lt_pow_succ_log_self (by norm_num) _
  have hs0 : (S.length - 1) * 2 ^ 0 ≤ S.length := by
    rw [pow_zero]
    omega
  have hroot := dcSharpGoCost_le h0 S.length (sharpDepth S.length ⌈1 / ε⌉₊)
    S 0 (Nat.zero_le _) hs0
  have hcost : dcSharpGoCost ε (sharpDepth S.length ⌈1 / ε⌉₊) S 0
      ≤ sharpDepth S.length ⌈1 / ε⌉₊
          * FLAT ⌈1 / ε⌉₊ S.length (sharpDepth S.length ⌈1 / ε⌉₊)
            (LGsharp ⌈1 / ε⌉₊ S.length (sharpDepth S.length ⌈1 / ε⌉₊))
        + 2 ^ sharpDepth S.length ⌈1 / ε⌉₊
          * BOTC ⌈1 / ε⌉₊ S.length (sharpDepth S.length ⌈1 / ε⌉₊)
            (LGsharp ⌈1 / ε⌉₊ S.length (sharpDepth S.length ⌈1 / ε⌉₊)) := by
    have e1 : dcSharpGoCost ε (sharpDepth S.length ⌈1 / ε⌉₊) S 0 * 2 ^ 0
        = dcSharpGoCost ε (sharpDepth S.length ⌈1 / ε⌉₊) S 0 := by
      rw [pow_zero]
      ring
    have e2 : sharpDepth S.length ⌈1 / ε⌉₊ - 0 = sharpDepth S.length ⌈1 / ε⌉₊ := by
      omega
    rw [e1, e2] at hroot
    exact hroot
  have hqlen : queryCost (dcSharp S ε)
      ≤ repSharp ⌈1 / ε⌉₊ S.length (sharpDepth S.length ⌈1 / ε⌉₊) 0 + 1 := by
    unfold queryCost
    have h1 := dcSharpGo_length h0 S.length (sharpDepth S.length ⌈1 / ε⌉₊)
      S 0 (Nat.zero_le _) hs0
    unfold dcSharp
    omega
  have hfc := final_collapse S.length ⌈1 / ε⌉₊ (sharpDepth S.length ⌈1 / ε⌉₊)
    hE hD_up hD_lo
    (dcSharpGoCost ε (sharpDepth S.length ⌈1 / ε⌉₊) S 0)
    (queryCost (dcSharp S ε))
    hcost hqlen
  unfold approxCountSharpCost
  omega

/-- **The complete sharp FPTAS**: correctness within `1+ε` *and* the
`Õ(n^2.5 ε^-1.5 + n² ε^-2)` operation bound, both machine-checked. -/
theorem fptasSharp (S : List ℕ) (C : ℕ) (ε : ℚ) (h0 : 0 < ε) (h1 : ε ≤ 1) :
    (countLe S C ≤ approxCountSharp S C ε ∧
      (approxCountSharp S C ε : ℚ) ≤ (1 + ε) * countLe S C) ∧
    approxCountSharpCost S C ε
      ≤ 10 ^ 7
        * LGsharp ⌈1 / ε⌉₊ S.length (sharpDepth S.length ⌈1 / ε⌉₊) ^ 2
        * (S.length + 2) ^ 2
        * (⌈1 / ε⌉₊ * (Nat.sqrt (S.length * ⌈1 / ε⌉₊) + 1) + ⌈1 / ε⌉₊ ^ 2) :=
  ⟨approxCountSharp_spec S C ε h0 h1, approxCountSharpCost_le S C ε h0 h1⟩

end SparseFun
