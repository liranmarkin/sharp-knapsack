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

end SparseFun
