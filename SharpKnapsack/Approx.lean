/-
# Sum approximations (paper Section 2)

This file formalizes Section 2 of "A Faster FPTAS for #Knapsack"
(Gawrychowski, Markin, Weimann, ICALP 2018): functions `ℕ → ℕ`, their prefix
sums `f^≤`, shifts `f|_w`, convolutions `f * g`, and the notion of a
(1+ε)-(sum) approximation, together with the paper's Lemma 6 (the four
operations on sum approximations).

One presentational difference from the paper: approximation is parametrized by
the whole factor `K : ℚ` (think `K = 1 + ε`) instead of by `ε`. This makes
composition of approximations literal multiplication of factors.
-/

import Mathlib

open Finset

/-- `prefixLe f x = ∑_{y ≤ x} f y`, the paper's `f^≤(x)` (Definition 3). -/
def prefixLe (f : ℕ → ℕ) (x : ℕ) : ℕ := ∑ y ∈ range (x + 1), f y

/-- `prefixLt f x = ∑_{y < x} f y`, the sum of all values strictly below `x`.
Not in the paper; used to state invariants of the sparsification scan. -/
def prefixLt (f : ℕ → ℕ) (x : ℕ) : ℕ := ∑ y ∈ range x, f y

/-- The shift `f|_w` of a function (paper Section 2):
`f|_w(x) = f(x - w)` for `x ≥ w`, and `0` below `w`. -/
def shiftFun (w : ℕ) (f : ℕ → ℕ) : ℕ → ℕ := fun x => if w ≤ x then f (x - w) else 0

/-- The convolution `(f * g)(x) = ∑_{y + z = x} f(y)·g(z)` (paper Section 2). -/
def convFun (f g : ℕ → ℕ) : ℕ → ℕ := fun x => ∑ y ∈ range (x + 1), f y * g (x - y)

/-- `F` approximates `f` within the multiplicative factor `K`
(paper Definition 4 with `K = 1 + ε`): `f ≤ F ≤ K·f` pointwise. -/
structure IsApprox (K : ℚ) (F f : ℕ → ℕ) : Prop where
  le : ∀ x, f x ≤ F x
  ge : ∀ x, (F x : ℚ) ≤ K * f x

/-- `F` is a `K`-sum approximation of `f` (paper Definition 5 with `K = 1 + ε`):
`F^≤` approximates `f^≤` within factor `K`. -/
def IsSumApprox (K : ℚ) (F f : ℕ → ℕ) : Prop := IsApprox K (prefixLe F) (prefixLe f)

/-! ## Basic facts about prefix sums, shifts, and convolutions -/

theorem prefixLe_succ (f : ℕ → ℕ) (x : ℕ) :
    prefixLe f (x + 1) = prefixLe f x + f (x + 1) := by
  simp [prefixLe, sum_range_succ]

theorem prefixLe_zero (f : ℕ → ℕ) : prefixLe f 0 = f 0 := by
  simp [prefixLe]

theorem prefixLe_mono (f : ℕ → ℕ) : Monotone (prefixLe f) := by
  intro a b hab
  induction hab with
  | refl => exact le_rfl
  | step _h ih =>
    exact le_trans ih (by rw [prefixLe_succ]; exact Nat.le_add_right _ _)

theorem prefixLe_add (f g : ℕ → ℕ) (x : ℕ) :
    prefixLe (fun y => f y + g y) x = prefixLe f x + prefixLe g x := by
  simp [prefixLe, sum_add_distrib]

/-- Prefix sums of a shifted function: `(f|_w)^≤(x) = f^≤(x - w)` for `x ≥ w`,
and `0` below `w`. Used in the proof of Lemma 6 (shifting). -/
theorem prefixLe_shiftFun (w : ℕ) (f : ℕ → ℕ) (x : ℕ) :
    prefixLe (shiftFun w f) x = if w ≤ x then prefixLe f (x - w) else 0 := by
  induction x with
  | zero =>
    rcases Nat.eq_zero_or_pos w with h | h
    · subst h; simp [prefixLe_zero, shiftFun]
    · have hw : ¬ w ≤ 0 := by omega
      simp [prefixLe_zero, shiftFun, hw]
  | succ x ih =>
    rw [prefixLe_succ, ih]
    by_cases h : w ≤ x
    · have h' : w ≤ x + 1 := le_trans h (Nat.le_succ x)
      have : x + 1 - w = (x - w) + 1 := by omega
      simp [h, h', shiftFun, this, prefixLe_succ]
    · by_cases h' : w ≤ x + 1
      · have hw : w = x + 1 := by omega
        subst hw
        simp [h, shiftFun, prefixLe_zero]
      · simp [h, h', shiftFun]

/-- Exchanging a convolution with a prefix sum:
`(f * g)^≤(x) = ∑_{y ≤ x} f(y) · g^≤(x - y)`.
This identity (and its mirror image) is the engine of the paper's proof of
Lemma 6 (convolution). -/
theorem prefixLe_convFun (f g : ℕ → ℕ) (x : ℕ) :
    prefixLe (convFun f g) x = ∑ y ∈ range (x + 1), f y * prefixLe g (x - y) := by
  induction x with
  | zero => simp [prefixLe_zero, convFun]
  | succ x ih =>
    rw [prefixLe_succ, ih, convFun]
    rw [sum_range_succ (fun y => f y * prefixLe g (x + 1 - y)),
        sum_range_succ (fun y => f y * g (x + 1 - y))]
    have hlast : x + 1 - (x + 1) = 0 := by omega
    rw [hlast]
    have : ∀ y ∈ range (x + 1),
        f y * prefixLe g (x + 1 - y) = f y * prefixLe g (x - y) + f y * g (x + 1 - y) := by
      intro y hy
      have hy' : y ≤ x := by simpa [Nat.lt_succ_iff] using mem_range.mp hy
      have : x + 1 - y = (x - y) + 1 := by omega
      rw [this, prefixLe_succ, Nat.mul_add]
    rw [sum_congr rfl this, sum_add_distrib, prefixLe_zero]
    ring

/-- Convolution is commutative. -/
theorem convFun_comm (f g : ℕ → ℕ) : convFun f g = convFun g f := by
  funext x
  unfold convFun
  rw [← sum_range_reflect]
  refine sum_congr rfl fun y hy => ?_
  have hy' : y ≤ x := by simpa [Nat.lt_succ_iff] using mem_range.mp hy
  have h1 : x + 1 - 1 - y = x - y := by omega
  have h2 : x - (x - y) = y := by omega
  rw [h1, h2, Nat.mul_comm]

/-- The mirror image of `prefixLe_convFun`:
`(f * g)^≤(x) = ∑_{y ≤ x} g(y) · f^≤(x - y)`. -/
theorem prefixLe_convFun' (f g : ℕ → ℕ) (x : ℕ) :
    prefixLe (convFun f g) x = ∑ y ∈ range (x + 1), g y * prefixLe f (x - y) := by
  rw [convFun_comm, prefixLe_convFun]

/-! ## Lemma 6: operations on sum approximations

The paper's Lemma 6 lists four operations. In the multiplicative-factor
formulation they read:

* **Approximation** (composition): a `K₁`-sum approximation of a `K₂`-sum
  approximation is a `K₁·K₂`-sum approximation.
* **Summation**: `F + G` is a `K`-sum approximation of `f + g`.
* **Shifting**: `F|_w` is a `K`-sum approximation of `f|_w`.
* **Convolution**: `F * G` is a `K₁·K₂`-sum approximation of `f * g`.
-/

namespace IsApprox

theorem refl (f : ℕ → ℕ) : IsApprox 1 f f :=
  ⟨fun _ => le_rfl, fun x => by simp⟩

/-- Weakening the factor: a `K₁`-approximation is a `K₂`-approximation
for any `K₂ ≥ K₁`. -/
theorem mono {K₁ K₂ : ℚ} {F f : ℕ → ℕ} (h : IsApprox K₁ F f) (hK : K₁ ≤ K₂) :
    IsApprox K₂ F f := by
  refine ⟨h.le, fun x => le_trans (h.ge x) ?_⟩
  exact mul_le_mul_of_nonneg_right hK (by positivity)

/-- Lemma 6, **Approximation**: composing approximations multiplies factors. -/
theorem comp {K₁ K₂ : ℚ} {F' F f : ℕ → ℕ} (h₁ : IsApprox K₁ F' F)
    (h₂ : IsApprox K₂ F f) (hK₁ : 0 ≤ K₁) : IsApprox (K₁ * K₂) F' f := by
  refine ⟨fun x => le_trans (h₂.le x) (h₁.le x), fun x => ?_⟩
  calc (F' x : ℚ) ≤ K₁ * F x := h₁.ge x
    _ ≤ K₁ * (K₂ * f x) := by
        exact mul_le_mul_of_nonneg_left (h₂.ge x) hK₁
    _ = K₁ * K₂ * f x := by ring

theorem one_le_of_pos {K : ℚ} {F f : ℕ → ℕ} (h : IsApprox K F f) {x : ℕ}
    (hx : 0 < f x) : 1 ≤ K := by
  have h1 : (f x : ℚ) ≤ F x := by exact_mod_cast h.le x
  have h2 : (F x : ℚ) ≤ K * f x := h.ge x
  have hfx : (0 : ℚ) < f x := by exact_mod_cast hx
  nlinarith

end IsApprox

namespace IsSumApprox

theorem refl (f : ℕ → ℕ) : IsSumApprox 1 f f := IsApprox.refl _

theorem mono {K₁ K₂ : ℚ} {F f : ℕ → ℕ} (h : IsSumApprox K₁ F f) (hK : K₁ ≤ K₂) :
    IsSumApprox K₂ F f := IsApprox.mono h hK

/-- Lemma 6, **Approximation**. -/
theorem comp {K₁ K₂ : ℚ} {F' F f : ℕ → ℕ} (h₁ : IsSumApprox K₁ F' F)
    (h₂ : IsSumApprox K₂ F f) (hK₁ : 0 ≤ K₁) : IsSumApprox (K₁ * K₂) F' f :=
  IsApprox.comp h₁ h₂ hK₁

/-- Lemma 6, **Summation**. -/
theorem add {K : ℚ} {F f G g : ℕ → ℕ} (hF : IsSumApprox K F f) (hG : IsSumApprox K G g) :
    IsSumApprox K (fun x => F x + G x) (fun x => f x + g x) := by
  constructor <;> intro x <;> rw [prefixLe_add, prefixLe_add]
  · exact Nat.add_le_add (hF.le x) (hG.le x)
  · push_cast
    calc (prefixLe F x : ℚ) + prefixLe G x ≤ K * prefixLe f x + K * prefixLe g x :=
          add_le_add (hF.ge x) (hG.ge x)
      _ = K * (prefixLe f x + prefixLe g x) := by ring

/-- Lemma 6, **Shifting**. -/
theorem shift {K : ℚ} {F f : ℕ → ℕ} (h : IsSumApprox K F f) (w : ℕ) :
    IsSumApprox K (shiftFun w F) (shiftFun w f) := by
  constructor <;> intro x <;> rw [prefixLe_shiftFun, prefixLe_shiftFun] <;> split
  · exact h.le _
  · exact le_rfl
  · exact h.ge _
  · simp

/-- Lemma 6, **Convolution**: `F * G` is a `K₁·K₂`-sum approximation of
`f * g`. The proof follows the paper's two chains of (in)equalities, using
`prefixLe_convFun` and its mirror image to exchange which factor is summed
against a prefix sum. -/
theorem conv {K₁ K₂ : ℚ} {F f G g : ℕ → ℕ} (hF : IsSumApprox K₁ F f)
    (hG : IsSumApprox K₂ G g) (hK₂ : 0 ≤ K₂) :
    IsSumApprox (K₁ * K₂) (convFun F G) (convFun f g) := by
  constructor <;> intro x
  · -- Lower bound: (f*g)^≤ ≤ (F*g)^≤ = (g*F)^≤ ≤ (F*G)^≤, reading the paper's
    -- first chain. All in ℕ.
    rw [prefixLe_convFun (f := f), prefixLe_convFun' (f := F)]
    calc ∑ y ∈ range (x + 1), f y * prefixLe g (x - y)
        ≤ ∑ y ∈ range (x + 1), f y * prefixLe G (x - y) := by
          exact sum_le_sum fun y _ => Nat.mul_le_mul_left _ (hG.le _)
      _ = ∑ y ∈ range (x + 1), G y * prefixLe f (x - y) := by
          rw [← prefixLe_convFun, ← prefixLe_convFun']
      _ ≤ ∑ y ∈ range (x + 1), G y * prefixLe F (x - y) := by
          exact sum_le_sum fun y _ => Nat.mul_le_mul_left _ (hF.le _)
  · -- Upper bound: (F*G)^≤ ≤ K₂·(F*g)^≤ = K₂·(g*F)^≤ ≤ K₁·K₂·(f*g)^≤,
    -- the paper's second chain. In ℚ after casting.
    rw [prefixLe_convFun (f := F), prefixLe_convFun (f := f)]
    push_cast
    calc (∑ y ∈ range (x + 1), (F y : ℚ) * prefixLe G (x - y))
        ≤ ∑ y ∈ range (x + 1), (F y : ℚ) * (K₂ * prefixLe g (x - y)) := by
          exact sum_le_sum fun y _ =>
            mul_le_mul_of_nonneg_left (hG.ge _) (by positivity)
      _ = K₂ * ∑ y ∈ range (x + 1), (F y : ℚ) * prefixLe g (x - y) := by
          rw [mul_sum]; exact sum_congr rfl fun y _ => by ring
      _ = K₂ * ∑ y ∈ range (x + 1), (g y : ℚ) * prefixLe F (x - y) := by
          congr 1
          exact_mod_cast (prefixLe_convFun F g x).symm.trans (prefixLe_convFun' F g x)
      _ ≤ K₂ * ∑ y ∈ range (x + 1), (g y : ℚ) * (K₁ * prefixLe f (x - y)) := by
          refine mul_le_mul_of_nonneg_left ?_ hK₂
          exact sum_le_sum fun y _ =>
            mul_le_mul_of_nonneg_left (hF.ge _) (by positivity)
      _ = K₁ * K₂ * ∑ y ∈ range (x + 1), (g y : ℚ) * prefixLe f (x - y) := by
          rw [mul_sum, mul_sum]; exact sum_congr rfl fun y _ => by ring
      _ = K₁ * K₂ * ∑ y ∈ range (x + 1), (f y : ℚ) * prefixLe g (x - y) := by
          congr 1
          exact_mod_cast (prefixLe_convFun' f g x).symm.trans (prefixLe_convFun f g x)

end IsSumApprox
