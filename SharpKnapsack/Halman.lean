/-
# The simplified Halman algorithm (paper Section 3)

Insert the items one at a time. Inserting item `w` into a set whose counting
function is approximated by `K` replaces `K` by `K + K|_w` (Lemma 9), which
doubles the representation - so each insertion is followed by a
sparsification. With per-item parameter `δ = ε/(2n)` the `n` accumulated
`(1+δ)` factors stay below `1+ε`.

**Deviation from the paper**: the paper picks `δ = (1+ε)^{1/n} - 1`, an
irrational number. We use `δ = ε/(2n)` and the Bernoulli-style bound
`(1+δ)^n · (1-nδ) ≤ 1`, keeping all arithmetic in `ℚ`. See the design notes
in `docs/`.

`halman_spec` is the end-to-end theorem: for `0 < ε ≤ 1`, the algorithm's
output is a `(1+ε)`-sum approximation of the exact counting function.
-/

import SharpKnapsack.Sparsify

open SparseFun

/-- The exact representation of `count []`: one subset (the empty one),
of weight `0`. -/
def emptyRep : SparseFun := [(0, 1)]

theorem emptyRep_eval : eval emptyRep = count ([] : List ℕ) := by
  funext x
  rcases Nat.eq_zero_or_pos x with h | h
  · subst h; simp [emptyRep, eval, single, count_nil]
  · have h1 : ¬ (0 : ℕ) = x := by omega
    have h2 : ¬ x = 0 := by omega
    simp [emptyRep, eval, single, count_nil, h1, h2]

theorem emptyRep_wf : WF emptyRep := by
  constructor
  · simp [emptyRep]
  · simp [emptyRep]

/-- Insert one item of weight `w`: `K ← sparsify δ (K + K|_w)` (Lemma 9 made
executable, followed by compression). -/
def insertItem (δ : ℚ) (K : SparseFun) (w : ℕ) : SparseFun :=
  sparsify δ (add K (shift w K))

/-- One insertion multiplies the approximation factor by `1 + δ`. -/
theorem insertItem_spec {A : ℚ} {K : SparseFun} {f : ℕ → ℕ} (δ : ℚ) (hδ : 0 ≤ δ)
    (hK : WF K) (happrox : IsSumApprox A (eval K) f) (w : ℕ) :
    IsSumApprox ((1 + δ) * A) (eval (insertItem δ K w))
      (fun x => f x + shiftFun w f x) ∧ WF (insertItem δ K w) := by
  have hsum : eval (add K (shift w K)) = fun x => eval K x + shiftFun w (eval K) x := by
    rw [add_spec, shift_spec]
  have happrox' : IsSumApprox A (eval (add K (shift w K)))
      (fun x => f x + shiftFun w f x) := by
    rw [hsum]
    exact IsSumApprox.add happrox (happrox.shift w)
  have hwf : WF (add K (shift w K)) := add_wf hK (shift_wf hK w)
  obtain ⟨hs, hswf⟩ := sparsify_spec δ hδ hwf
  exact ⟨IsSumApprox.comp hs happrox' (by linarith), hswf⟩

/-- The insertion loop: process the items right to left, so that the recursion
mirrors `count_cons` (Lemma 9) directly. -/
def halmanGo (δ : ℚ) : List ℕ → SparseFun
  | [] => emptyRep
  | w :: S => insertItem δ (halmanGo δ S) w

theorem halmanGo_spec (δ : ℚ) (hδ : 0 ≤ δ) (S : List ℕ) :
    IsSumApprox ((1 + δ) ^ S.length) (eval (halmanGo δ S)) (count S) ∧
    WF (halmanGo δ S) := by
  induction S with
  | nil =>
    constructor
    · rw [show eval (halmanGo δ []) = count ([] : List ℕ) from emptyRep_eval]
      simpa using IsSumApprox.refl (count [])
    · exact emptyRep_wf
  | cons w S ih =>
    obtain ⟨happrox, hwf⟩ := ih
    obtain ⟨h1, h2⟩ := insertItem_spec δ hδ hwf happrox w
    constructor
    · have hc : count (w :: S) = fun x => count S x + shiftFun w (count S) x :=
        funext (count_cons w S)
      rw [show halmanGo δ (w :: S) = insertItem δ (halmanGo δ S) w from rfl, hc]
      have hpow : (1 + δ) ^ (w :: S).length = (1 + δ) * (1 + δ) ^ S.length := by
        simp [pow_succ]
        ring
      rw [hpow]
      exact h1
    · exact h2

/-- Bernoulli-style bound, entirely in `ℚ`: `(1+δ)^n · (1 - nδ) ≤ 1`. -/
theorem pow_one_add_mul_le (δ : ℚ) (hδ : 0 ≤ δ) (n : ℕ) :
    (1 + δ) ^ n * (1 - n * δ) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hpow : (0 : ℚ) ≤ (1 + δ) ^ n := by positivity
    have hn0 : (0 : ℚ) ≤ (n : ℚ) := Nat.cast_nonneg n
    have hstep : (1 + δ) * (1 - ((n : ℚ) + 1) * δ) ≤ 1 - n * δ := by
      nlinarith [sq_nonneg δ]
    push_cast
    calc (1 + δ) ^ (n + 1) * (1 - ((n : ℚ) + 1) * δ)
        = (1 + δ) ^ n * ((1 + δ) * (1 - ((n : ℚ) + 1) * δ)) := by ring
      _ ≤ (1 + δ) ^ n * (1 - (n : ℚ) * δ) := mul_le_mul_of_nonneg_left hstep hpow
      _ ≤ 1 := ih

/-- The full algorithm of Section 3 with overall target factor `1 + ε`. -/
def halman (S : List ℕ) (ε : ℚ) : SparseFun :=
  halmanGo (ε / (2 * S.length)) S

/-- **Section 3, end-to-end**: for `0 < ε ≤ 1`, `halman S ε` is a
`(1+ε)`-sum approximation of the exact counting function `count S`, with a
well-formed representation. -/
theorem halman_spec (S : List ℕ) (ε : ℚ) (h0 : 0 < ε) (h1 : ε ≤ 1) :
    IsSumApprox (1 + ε) (eval (halman S ε)) (count S) ∧ WF (halman S ε) := by
  set n := S.length with hn
  set δ := ε / (2 * n) with hδdef
  have hδ : 0 ≤ δ := by
    apply div_nonneg (le_of_lt h0)
    positivity
  obtain ⟨happrox, hwf⟩ := halmanGo_spec δ hδ S
  refine ⟨happrox.mono ?_, hwf⟩
  -- (1+δ)^n ≤ 1+ε.
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · have hS : S.length = 0 := by omega
    rw [hS, pow_zero]
    linarith
  · have hne : (2 * n : ℚ) ≠ 0 := by
      have : (0 : ℚ) < n := by exact_mod_cast hnpos
      positivity
    have hnδ : (n : ℚ) * δ = ε / 2 := by
      rw [hδdef]
      field_simp
    have hb := pow_one_add_mul_le δ hδ n
    rw [hnδ] at hb
    have hpow : (0 : ℚ) ≤ (1 + δ) ^ n := by positivity
    nlinarith [hb, hpow]
