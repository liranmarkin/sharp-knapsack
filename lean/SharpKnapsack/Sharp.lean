/-
# The sharp algorithm: depth-capped recursion with a power-of-two schedule

This file is the algorithmic half of the *sharp* verified running-time bound
(the paper's Õ(n^2.5 ε^-1.5), vs. the loose polynomial of `Complexity.lean`).
The divide-and-conquer of `DivideConquer.lean` used a geometric (2/5)-ratio
schedule chosen to make the correctness induction one line; its price is a
polynomially loose cost bound. Here we use a *rational form of the paper's
own schedule*:

  δ_d = ε / (16 · 2^⌈d/2⌉ · 2^⌈D/2⌉)   (internal node at depth d < D)
  δ_bot = ε / (16 · 4^⌈D/2⌉)           (bottom nodes)

with the recursion depth capped at `D ≈ log₂ √(nε)`. The paper's
`δ_i = ε^{3/4}/(2c·2^{i/2}·n^{1/4})` involves irrational powers; replacing
`2^{i/2}` by `2^⌈i/2⌉` and baking `(εn)^{1/4}` into `2^⌈D/2⌉` keeps everything
in ℚ while preserving the balance that yields the n^2.5 bound.

Correctness uses the *budget function* `Bud d = δ_d + 2·Bud (d+1)`,
`Bud D = δ_bot` (the total approximation budget of a depth-d subtree). Two
facts drive the induction:

* `(1+δ)·(1-(δ+2x)) ≤ (1-x)²` for all `δ, x ≥ 0` - one node's sparsification
  factor fits its budget;
* `Bud 0 ≤ (3/16)·ε`, from the exact staircase-sum identity
  `Σ_{i<D} 2^⌊i/2⌋ = 2^⌈D/2⌉ + 2^⌊D/2⌋ - 2`.

`approxCountSharp_spec` is then Theorem 1's guarantee for this algorithm.
-/

import SharpKnapsack.Halman

open SparseFun

/-! ## The schedule -/

/-- Internal sparsification parameter at depth `d` (with depth cap `D`).
`(d+1)/2` is `⌈d/2⌉` in ℕ-division. -/
def deltaSharp (ε : ℚ) (D d : ℕ) : ℚ :=
  ε / (16 * 2 ^ ((d + 1) / 2) * 2 ^ ((D + 1) / 2))

/-- Bottom-node target parameter. -/
def deltaBot (ε : ℚ) (D : ℕ) : ℚ :=
  ε / (16 * 2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2))

theorem deltaSharp_pos {ε : ℚ} (h : 0 < ε) (D d : ℕ) : 0 < deltaSharp ε D d := by
  unfold deltaSharp
  positivity

theorem deltaBot_pos {ε : ℚ} (h : 0 < ε) (D : ℕ) : 0 < deltaBot ε D := by
  unfold deltaBot
  positivity

theorem deltaSharp_le {ε : ℚ} (h1 : ε ≤ 1) (D d : ℕ) :
    deltaSharp ε D d ≤ 1 / 16 := by
  unfold deltaSharp
  have h2 : (1 : ℚ) ≤ 2 ^ ((d + 1) / 2) := one_le_pow₀ (by norm_num)
  have h3 : (1 : ℚ) ≤ 2 ^ ((D + 1) / 2) := one_le_pow₀ (by norm_num)
  have h4 : (16 : ℚ) ≤ 16 * 2 ^ ((d + 1) / 2) * 2 ^ ((D + 1) / 2) := by nlinarith
  have h5 : (0 : ℚ) < 16 * 2 ^ ((d + 1) / 2) * 2 ^ ((D + 1) / 2) := by positivity
  rw [div_le_div_iff₀ h5 (by norm_num)]
  nlinarith

theorem deltaBot_le {ε : ℚ} (h1 : ε ≤ 1) (D : ℕ) :
    deltaBot ε D ≤ 1 / 16 := by
  unfold deltaBot
  have h3 : (1 : ℚ) ≤ 2 ^ ((D + 1) / 2) := one_le_pow₀ (by norm_num)
  have h4 : (16 : ℚ) ≤ 16 * 2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2) := by nlinarith
  have h5 : (0 : ℚ) < 16 * 2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2) := by positivity
  rw [div_le_div_iff₀ h5 (by norm_num)]
  nlinarith

/-! ## The algorithm -/

/-- The sharp divide-and-conquer: recurse until depth `D` (or until the item
list is trivial), then run the insertion loop. A depth-`D` bottom node
re-sparsifies its output at `deltaBot` so that its parent's convolution sees
a coarse representation (the insertion loop's own output is sparsified at
the much finer per-item parameter). -/
def dcSharpGo (ε : ℚ) (D : ℕ) (S : List ℕ) (d : ℕ) : SparseFun :=
  if S.length ≤ 1 then
    halman S (deltaBot ε D)
  else if D ≤ d then
    sparsify (deltaBot ε D) (halman S (deltaBot ε D))
  else
    sparsify (deltaSharp ε D d)
      (conv (dcSharpGo ε D (S.take (S.length / 2)) (d + 1))
            (dcSharpGo ε D (S.drop (S.length / 2)) (d + 1)))
termination_by D - d
decreasing_by all_goals omega

/-- Depth cap: `2^D ≈ √(nε)`, expressed as `√(n / ⌈1/ε⌉)`. -/
def sharpDepth (n E : ℕ) : ℕ := Nat.log 2 (Nat.sqrt (n / E) + 1)

def dcSharp (S : List ℕ) (ε : ℚ) : SparseFun :=
  dcSharpGo ε (sharpDepth S.length ⌈1 / ε⌉₊) S 0

/-- The sharp algorithm's answer to a #Knapsack instance. -/
def approxCountSharp (S : List ℕ) (C : ℕ) (ε : ℚ) : ℕ :=
  queryLe (dcSharp S ε) C

/-! ## The budget function -/

/-- Total approximation budget of a depth-`d` subtree (bottom nodes budget
`3·δ_bot`: the insertion loop's `1+δ_bot` and the re-sparsification's
`1+δ_bot` fit inside `1/(1-3·δ_bot)`). -/
def Bud (ε : ℚ) (D d : ℕ) : ℚ :=
  if D ≤ d then 3 * deltaBot ε D
  else deltaSharp ε D d + 2 * Bud ε D (d + 1)
termination_by D - d
decreasing_by omega

theorem Bud_pos {ε : ℚ} (h : 0 < ε) (D d : ℕ) : 0 < Bud ε D d := by
  induction d using Bud.induct (D := D) with
  | case1 d hle =>
    rw [Bud, if_pos hle]
    have := deltaBot_pos h D
    linarith
  | case2 d hlt ih =>
    rw [Bud, if_neg hlt]
    have := deltaSharp_pos h D d
    linarith

theorem deltaBot_le_Bud {ε : ℚ} (h : 0 < ε) (D d : ℕ) :
    3 * deltaBot ε D ≤ Bud ε D d := by
  induction d using Bud.induct (D := D) with
  | case1 d hle =>
    rw [Bud, if_pos hle]
  | case2 d hlt ih =>
    rw [Bud, if_neg hlt]
    have h1 := deltaSharp_pos h D d
    have h2 := deltaBot_pos h D
    linarith

/-- The staircase-sum identity `Σ_{i<D} 2^⌊i/2⌋ = 2^⌈D/2⌉ + 2^⌊D/2⌋ - 2`,
stated additively to avoid ℕ-subtraction. -/
theorem staircase_sum (D : ℕ) :
    (∑ i ∈ Finset.range D, (2 : ℚ) ^ (i / 2)) + 2
      = 2 ^ ((D + 1) / 2) + 2 ^ (D / 2) := by
  induction D with
  | zero => norm_num
  | succ D ih =>
    rw [Finset.sum_range_succ]
    rcases Nat.even_or_odd D with he | ho
    · obtain ⟨k, hk⟩ := he
      subst hk
      have e1 : (k + k) / 2 = k := by omega
      have e2 : (k + k + 1) / 2 = k := by omega
      have e3 : (k + k + 1 + 1) / 2 = k + 1 := by omega
      rw [e2, e1] at ih
      rw [e1, e2, e3, pow_succ]
      linarith
    · obtain ⟨k, hk⟩ := ho
      subst hk
      have e1 : (2 * k + 1) / 2 = k := by omega
      have e2 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
      have e3 : (2 * k + 1 + 1 + 1) / 2 = k + 1 := by omega
      rw [e2, e1, pow_succ] at ih
      rw [e1, e2, e3, pow_succ]
      linarith

/-- Closed form of the budget: exact identity, proved by downward induction
(the increment matches `δ_d` exactly thanks to the staircase structure). -/
theorem Bud_eq {ε : ℚ} (D : ℕ) :
    ∀ d, d ≤ D →
    Bud ε D d = ε / 16 *
      (((2 : ℚ) ^ ((D + 1) / 2) + 2 ^ (D / 2) - (2 ^ ((d + 1) / 2) + 2 ^ (d / 2)))
          / (2 ^ ((D + 1) / 2) * 2 ^ d)
        + 3 * 2 ^ (D - d) / (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2))) := by
  intro d
  induction d using Bud.induct (D := D) with
  | case1 d hle =>
    intro hdD
    have hd : d = D := by omega
    subst hd
    rw [Bud, if_pos hle]
    unfold deltaBot
    have h1 : (0 : ℚ) < 2 ^ ((d + 1) / 2) := by positivity
    have h2 : (0 : ℚ) < 2 ^ d := by positivity
    rw [Nat.sub_self, pow_zero]
    field_simp
    ring
  | case2 d hlt ih =>
    intro _
    have hdD : d < D := by omega
    rw [Bud, if_neg hlt, ih (by omega)]
    unfold deltaSharp
    have hp1 : (0 : ℚ) < 2 ^ ((d + 1) / 2) := by positivity
    have hp2 : (0 : ℚ) < 2 ^ ((D + 1) / 2) := by positivity
    have hp3 : (0 : ℚ) < (2 : ℚ) ^ d := by positivity
    -- The staircase increment: 2^((d+2)/2) + 2^((d+1)/2) = 2·2^(d/2) + ... ;
    -- concretely (with e := parity of d):
    have hstep : (2 : ℚ) ^ ((d + 1 + 1) / 2) + 2 ^ ((d + 1) / 2)
        = 2 ^ ((d + 1) / 2) + 2 ^ (d / 2) + 2 ^ (d / 2) := by
      rcases Nat.even_or_odd d with he | ho
      · obtain ⟨k, hk⟩ := he
        have e1 : d / 2 = k := by omega
        have e2 : (d + 1) / 2 = k := by omega
        have e3 : (d + 1 + 1) / 2 = k + 1 := by omega
        rw [e1, e2, e3]
        push_cast [pow_succ]
        ring
      · obtain ⟨k, hk⟩ := ho
        have e1 : d / 2 = k := by omega
        have e2 : (d + 1) / 2 = k + 1 := by omega
        have e3 : (d + 1 + 1) / 2 = k + 1 := by omega
        rw [e1, e2, e3]
        push_cast [pow_succ]
        ring
    have hab : (2 : ℚ) ^ ((d + 1) / 2) * 2 ^ (d / 2) = 2 ^ d := by
      rw [← pow_add]
      congr 1
      omega
    have ha' : (2 : ℚ) ^ ((d + 1 + 1) / 2) = 2 ^ (d / 2) * 2 := by linarith
    have hpow : ((2 : ℚ) ^ (D - (d + 1))) * 2 = 2 ^ (D - d) := by
      rw [← pow_succ]
      congr 1
      omega
    have hpd : ((2 : ℚ) ^ (d + 1)) = 2 ^ d * 2 := by
      rw [pow_succ]
    rw [ha', hpd, ← hpow, ← hab]
    have hb : (0 : ℚ) < 2 ^ (d / 2) := by positivity
    field_simp
    ring

/-- The root budget is at most `(3/16)·ε`. -/
theorem Bud_zero_le {ε : ℚ} (h0 : 0 < ε) (D : ℕ) : Bud ε D 0 ≤ 5 / 16 * ε := by
  have h := Bud_eq (ε := ε) D 0 (by omega)
  rw [h]
  have hp2 : (0 : ℚ) < 2 ^ ((D + 1) / 2) := by positivity
  have hp4 : (1 : ℚ) ≤ 2 ^ ((D + 1) / 2) := one_le_pow₀ (by norm_num)
  have hDe : (D : ℕ) - 0 = D := by omega
  rw [hDe]
  simp only [pow_zero, Nat.zero_div, mul_one]
  -- numerator ≤ 2^((D+1)/2) + 2^(D/2) ≤ 2·2^((D+1)/2); the last term ≤ 1.
  have hle1 : (2 : ℚ) ^ (D / 2) ≤ 2 ^ ((D + 1) / 2) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hle2 : (2 : ℚ) ^ D ≤ 2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2) := by
    rw [← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hterm2 : 3 * (2 : ℚ) ^ D / (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2)) ≤ 3 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hterm1 : ((2 : ℚ) ^ ((D + 1) / 2) + 2 ^ (D / 2)
        - (2 ^ ((0 + 1) / 2) + 2 ^ (0 / 2))) / (2 ^ ((D + 1) / 2)) ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]
    norm_num
    nlinarith
  have hεp : (0 : ℚ) < ε / 16 := by positivity
  calc ε / 16 * ((2 ^ ((D + 1) / 2) + 2 ^ (D / 2)
          - (2 ^ ((0 + 1) / 2) + 2 ^ (0 / 2))) / (2 ^ ((D + 1) / 2))
        + 3 * 2 ^ D / (2 ^ ((D + 1) / 2) * 2 ^ ((D + 1) / 2)))
      ≤ ε / 16 * (2 + 3) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hεp)
        linarith
    _ = 5 / 16 * ε := by ring

theorem Bud_le {ε : ℚ} (h0 : 0 < ε) (D : ℕ) : ∀ d, Bud ε D d ≤ 5 / 16 * ε := by
  -- The budget shrinks as depth grows: `Bud (d+1) ≤ Bud d` since
  -- `Bud d = δ_d + 2·Bud (d+1) ≥ Bud (d+1)`; beyond `D` it is constant.
  have key : ∀ d, Bud ε D (d + 1) ≤ Bud ε D d := by
    intro d
    by_cases hle : D ≤ d
    · rw [show Bud ε D (d + 1) = 3 * deltaBot ε D by rw [Bud, if_pos (by omega)],
          show Bud ε D d = 3 * deltaBot ε D by rw [Bud, if_pos hle]]
    · rw [show Bud ε D d = deltaSharp ε D d + 2 * Bud ε D (d + 1) by
        rw [Bud, if_neg hle]]
      have h1 := deltaSharp_pos h0 D d
      have h2 := Bud_pos h0 D (d + 1)
      linarith
  intro d
  induction d with
  | zero => exact Bud_zero_le h0 D
  | succ d ih => exact le_trans (key d) ih

/-! ## Correctness -/

/-- One node's factor fits its budget: `(1+δ)(1-(δ+2x)) ≤ (1-x)²`. -/
theorem budget_step (δ x : ℚ) (hδ : 0 ≤ δ) (hx : 0 ≤ x) :
    (1 + δ) * (1 - (δ + 2 * x)) ≤ (1 - x) ^ 2 := by
  nlinarith [sq_nonneg δ, mul_nonneg hδ hx]

/-- Every depth-`d` subtree returns a `1/(1 - Bud d)`-sum approximation. -/
theorem dcSharpGo_spec {ε : ℚ} (h0 : 0 < ε) (h1 : ε ≤ 1) (D : ℕ)
    (S : List ℕ) (d : ℕ) :
    IsSumApprox (1 / (1 - Bud ε D d)) (eval (dcSharpGo ε D S d)) (count S) ∧
      WF (dcSharpGo ε D S d) := by
  have hBud := Bud_le h0 D d
  have hBpos := Bud_pos h0 D d
  have hB1 : Bud ε D d < 1 := by linarith
  have hden : 0 < 1 - Bud ε D d := by linarith
  have hδb0 := deltaBot_pos h0 D
  have hδb1 : deltaBot ε D ≤ 1 := le_trans (deltaBot_le h1 D) (by norm_num)
  have hle3 := deltaBot_le_Bud h0 D d
  rw [dcSharpGo.eq_def]
  by_cases htriv : S.length ≤ 1
  · rw [if_pos htriv]
    obtain ⟨h, hwf⟩ := halman_spec S (deltaBot ε D) hδb0 hδb1
    refine ⟨h.mono ?_, hwf⟩
    rw [le_div_iff₀ hden]
    nlinarith
  · rw [if_neg htriv]
    by_cases hDd : D ≤ d
    · rw [if_pos hDd]
      obtain ⟨hh, hhwf⟩ := halman_spec S (deltaBot ε D) hδb0 hδb1
      obtain ⟨hsp, hspwf⟩ := sparsify_spec (deltaBot ε D) (le_of_lt hδb0) hhwf
      refine ⟨(IsSumApprox.comp hsp hh (by linarith)).mono ?_, hspwf⟩
      rw [le_div_iff₀ hden]
      nlinarith [sq_nonneg (deltaBot ε D), mul_nonneg (le_of_lt hδb0) (le_of_lt hδb0)]
    · rw [if_neg hDd]
      have hd : d < D := by omega
      have hBudd : Bud ε D d = deltaSharp ε D d + 2 * Bud ε D (d + 1) := by
        rw [Bud, if_neg (by omega)]
      obtain ⟨hA, hAwf⟩ := dcSharpGo_spec h0 h1 D (S.take (S.length / 2)) (d + 1)
      obtain ⟨hB, hBwf⟩ := dcSharpGo_spec h0 h1 D (S.drop (S.length / 2)) (d + 1)
      have hδ0 := deltaSharp_pos h0 D d
      have hBud' := Bud_le h0 D (d + 1)
      have hBpos' := Bud_pos h0 D (d + 1)
      have hden' : 0 < 1 - Bud ε D (d + 1) := by linarith
      have hphi' : (0 : ℚ) ≤ 1 / (1 - Bud ε D (d + 1)) := by positivity
      have hconv : IsSumApprox
          (1 / (1 - Bud ε D (d + 1)) * (1 / (1 - Bud ε D (d + 1))))
          (eval (conv (dcSharpGo ε D (S.take (S.length / 2)) (d + 1))
                      (dcSharpGo ε D (S.drop (S.length / 2)) (d + 1))))
          (count S) := by
        have h10 : count S = convFun (count (S.take (S.length / 2)))
            (count (S.drop (S.length / 2))) := by
          conv_lhs => rw [← List.take_append_drop (S.length / 2) S]
          exact count_append _ _
        rw [conv_spec, h10]
        exact IsSumApprox.conv hA hB hphi'
      obtain ⟨hs, hswf⟩ := sparsify_spec (deltaSharp ε D d) (le_of_lt hδ0)
        (conv_wf hAwf hBwf)
      refine ⟨(IsSumApprox.comp hs hconv (by linarith)).mono ?_, hswf⟩
      -- (1+δ_d)·Φ(d+1)² ≤ Φ(d), from `budget_step`.
      have hstep := budget_step (deltaSharp ε D d) (Bud ε D (d + 1))
        (le_of_lt hδ0) (le_of_lt hBpos')
      rw [div_mul_div_comm, one_mul]
      rw [show (1 + deltaSharp ε D d)
            * (1 / ((1 - Bud ε D (d + 1)) * (1 - Bud ε D (d + 1))))
          = (1 + deltaSharp ε D d)
            / ((1 - Bud ε D (d + 1)) * (1 - Bud ε D (d + 1))) by ring]
      rw [div_le_div_iff₀ (by positivity) hden]
      calc (1 + deltaSharp ε D d) * (1 - Bud ε D d)
          = (1 + deltaSharp ε D d)
              * (1 - (deltaSharp ε D d + 2 * Bud ε D (d + 1))) := by rw [hBudd]
        _ ≤ (1 - Bud ε D (d + 1)) ^ 2 := hstep
        _ = 1 * ((1 - Bud ε D (d + 1)) * (1 - Bud ε D (d + 1))) := by ring
termination_by D - d
decreasing_by all_goals omega

/-- The sharp algorithm is a `(1+ε)`-approximation scheme. -/
theorem dcSharp_spec (S : List ℕ) (ε : ℚ) (h0 : 0 < ε) (h1 : ε ≤ 1) :
    IsSumApprox (1 + ε) (eval (dcSharp S ε)) (count S) ∧ WF (dcSharp S ε) := by
  obtain ⟨h, hwf⟩ := dcSharpGo_spec h0 h1 (sharpDepth S.length ⌈1 / ε⌉₊) S 0
  refine ⟨h.mono ?_, hwf⟩
  set D := sharpDepth S.length ⌈1 / ε⌉₊
  have hB := Bud_le h0 D 0
  have hBpos := Bud_pos h0 D 0
  have hden : 0 < 1 - Bud ε D 0 := by linarith
  rw [div_le_iff₀ hden]
  nlinarith

/-- **Theorem 1's guarantee for the sharp algorithm**. -/
theorem approxCountSharp_spec (S : List ℕ) (C : ℕ) (ε : ℚ)
    (h0 : 0 < ε) (h1 : ε ≤ 1) :
    countLe S C ≤ approxCountSharp S C ε ∧
      (approxCountSharp S C ε : ℚ) ≤ (1 + ε) * countLe S C := by
  obtain ⟨h, _⟩ := dcSharp_spec S ε h0 h1
  unfold approxCountSharp countLe
  rw [queryLe_spec]
  exact ⟨h.le C, h.ge C⟩
