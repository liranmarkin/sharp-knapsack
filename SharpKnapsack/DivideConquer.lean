/-
# The divide-and-conquer algorithm and main theorem (paper Section 4)

Instead of inserting items one at a time, split the item list in the middle,
solve both halves recursively, and merge with a convolution (Lemma 10),
sparsifying after each merge. Small sets (below a threshold of about `√n`)
are handled by the Section 3 insertion loop.

The approximation budget: a node at recursion depth `d` sparsifies with

  `δ(d) = (ε/20)·(2/5)^d`.

**Deviation from the paper**: the paper's schedule `δ_i = ε^¾/(2c·2^{i/2}·n^¼)`
involves irrational powers, and its analysis runs through real exponentials.
Any geometric schedule with ratio `< 1/2` admits the same conclusion with a
purely rational, one-step induction: writing `Φ(d) = 1/(1 - 5·δ(d))`, the key
identity `5·δ(d+1) = 2·δ(d)` gives

  `(1 + δ(d)) · Φ(d+1)² ≤ Φ(d)`   (`phi_step` below),

so by induction over the recursion tree every depth-`d` node returns a
`Φ(d)`-sum approximation, and `Φ(0) = 1/(1 - ε/4) ≤ 1 + ε`. The algorithm's
structure - middle recursion, convolution merge, geometrically finer
sparsification with depth - is exactly the paper's; only the constants
differ (the paper's ratio `2^{-1/2}` is tuned for the `O(n^{2.5})` running
time bound, which this development does not verify).

The final statement `approxCount_spec` is the correctness half of the
paper's **Theorem 1**.
-/

import SharpKnapsack.Halman

open SparseFun

/-- The sparsification parameter at recursion depth `d`. -/
def deltaAt (ε : ℚ) (d : ℕ) : ℚ := ε / 20 * (2 / 5) ^ d

theorem deltaAt_pos {ε : ℚ} (h0 : 0 < ε) (d : ℕ) : 0 < deltaAt ε d := by
  unfold deltaAt
  positivity

theorem deltaAt_le {ε : ℚ} (h0 : 0 < ε) (h1 : ε ≤ 1) (d : ℕ) :
    deltaAt ε d ≤ 1 / 20 := by
  unfold deltaAt
  have hp : (2 / 5 : ℚ) ^ d ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  have h2 : ε / 20 * (2 / 5) ^ d ≤ ε / 20 * 1 :=
    mul_le_mul_of_nonneg_left hp (by positivity)
  have h3 : ε / 20 ≤ 1 / 20 := by linarith
  linarith

theorem deltaAt_succ (ε : ℚ) (d : ℕ) :
    deltaAt ε (d + 1) = 2 / 5 * deltaAt ε d := by
  unfold deltaAt
  ring

/-- The per-depth budget inequality: `(1+δ(d)) · Φ(d+1)² ≤ Φ(d)` where
`Φ(d) = 1/(1 - 5·δ(d))`. This single step, iterated along the recursion
tree, replaces the paper's global product estimate. -/
theorem phi_step {ε : ℚ} (h0 : 0 < ε) (h1 : ε ≤ 1) (d : ℕ) :
    (1 + deltaAt ε d) *
        (1 / (1 - 5 * deltaAt ε (d + 1)) * (1 / (1 - 5 * deltaAt ε (d + 1))))
      ≤ 1 / (1 - 5 * deltaAt ε d) := by
  set a := deltaAt ε d with ha
  have hpos : 0 < a := deltaAt_pos h0 d
  have hle : a ≤ 1 / 20 := deltaAt_le h0 h1 d
  have hsucc : deltaAt ε (d + 1) = 2 / 5 * a := deltaAt_succ ε d
  rw [hsucc]
  have e1 : 1 - 5 * (2 / 5 * a) = 1 - 2 * a := by ring
  rw [e1]
  have h2a : 0 < 1 - 2 * a := by linarith
  have h5a : 0 < 1 - 5 * a := by linarith
  have e2 : (1 + a) * (1 / (1 - 2 * a) * (1 / (1 - 2 * a)))
      = (1 + a) / ((1 - 2 * a) * (1 - 2 * a)) := by
    field_simp
  rw [e2, div_le_div_iff₀ (by positivity) h5a]
  nlinarith [sq_nonneg a]

/-- A bottom node's factor fits the budget: `1 + δ ≤ 1/(1 - 5δ)`. -/
theorem one_add_le_phi {δ : ℚ} (hδ : 0 ≤ δ) (h : 5 * δ < 1) :
    1 + δ ≤ 1 / (1 - 5 * δ) := by
  rw [le_div_iff₀ (by linarith)]
  nlinarith

/-- The divide-and-conquer recursion. `T` is the size threshold below which
the Section 3 insertion loop takes over (`max 1 T` keeps the recursion
well-founded for any `T`); `d` is the current depth. -/
def dcGo (ε : ℚ) (T : ℕ) (S : List ℕ) (d : ℕ) : SparseFun :=
  if S.length ≤ max 1 T then
    halman S (deltaAt ε d)
  else
    sparsify (deltaAt ε d)
      (conv (dcGo ε T (S.take (S.length / 2)) (d + 1))
            (dcGo ε T (S.drop (S.length / 2)) (d + 1)))
termination_by S.length
decreasing_by
  · simp only [List.length_take]
    omega
  · simp only [List.length_drop]
    omega

/-- The algorithm of Theorem 1: threshold `√n`, starting depth `0`. -/
def dc (S : List ℕ) (ε : ℚ) : SparseFun := dcGo ε (Nat.sqrt S.length) S 0

/-- Every depth-`d` node returns a `Φ(d)`-sum approximation of the counting
function of its item list, where `Φ(d) = 1/(1 - 5·δ(d))`. -/
theorem dcGo_spec (ε : ℚ) (h0 : 0 < ε) (h1 : ε ≤ 1) (T : ℕ) (S : List ℕ) (d : ℕ) :
    IsSumApprox (1 / (1 - 5 * deltaAt ε d)) (eval (dcGo ε T S d)) (count S) ∧
      WF (dcGo ε T S d) := by
  have hδpos : 0 < deltaAt ε d := deltaAt_pos h0 d
  have hδle : deltaAt ε d ≤ 1 / 20 := deltaAt_le h0 h1 d
  have h5 : 0 < 1 - 5 * deltaAt ε d := by linarith
  rw [dcGo.eq_def]
  by_cases hlen : S.length ≤ max 1 T
  · rw [if_pos hlen]
    obtain ⟨h, hwf⟩ := halman_spec S (deltaAt ε d) hδpos (by linarith)
    exact ⟨h.mono (one_add_le_phi (le_of_lt hδpos) (by linarith)), hwf⟩
  · rw [if_neg hlen]
    obtain ⟨hA, hAwf⟩ := dcGo_spec ε h0 h1 T (S.take (S.length / 2)) (d + 1)
    obtain ⟨hB, hBwf⟩ := dcGo_spec ε h0 h1 T (S.drop (S.length / 2)) (d + 1)
    have hδpos' : 0 < deltaAt ε (d + 1) := deltaAt_pos h0 (d + 1)
    have hδle' : deltaAt ε (d + 1) ≤ 1 / 20 := deltaAt_le h0 h1 (d + 1)
    have h5' : 0 < 1 - 5 * deltaAt ε (d + 1) := by linarith
    have hphi' : (0 : ℚ) ≤ 1 / (1 - 5 * deltaAt ε (d + 1)) := by positivity
    -- Convolution of the two halves (Lemma 10 + Lemma 6).
    have hconv : IsSumApprox
        (1 / (1 - 5 * deltaAt ε (d + 1)) * (1 / (1 - 5 * deltaAt ε (d + 1))))
        (eval (conv (dcGo ε T (S.take (S.length / 2)) (d + 1))
                    (dcGo ε T (S.drop (S.length / 2)) (d + 1))))
        (count S) := by
      have h10 : count S = convFun (count (S.take (S.length / 2)))
          (count (S.drop (S.length / 2))) := by
        conv_lhs => rw [← List.take_append_drop (S.length / 2) S]
        exact count_append _ _
      rw [conv_spec, h10]
      exact IsSumApprox.conv hA hB hphi'
    -- Sparsify the merge and compose the factors.
    obtain ⟨hs, hswf⟩ := sparsify_spec (deltaAt ε d) (le_of_lt hδpos)
      (conv_wf hAwf hBwf)
    refine ⟨(IsSumApprox.comp hs hconv (by linarith)).mono ?_, hswf⟩
    exact phi_step h0 h1 d
termination_by S.length
decreasing_by
  · simp only [List.length_take]
    omega
  · simp only [List.length_drop]
    omega

/-- The divide-and-conquer algorithm is a `(1+ε)`-approximation scheme. -/
theorem dc_spec (S : List ℕ) (ε : ℚ) (h0 : 0 < ε) (h1 : ε ≤ 1) :
    IsSumApprox (1 + ε) (eval (dc S ε)) (count S) ∧ WF (dc S ε) := by
  obtain ⟨h, hwf⟩ := dcGo_spec ε h0 h1 (Nat.sqrt S.length) S 0
  refine ⟨h.mono ?_, hwf⟩
  have e0 : deltaAt ε 0 = ε / 20 := by
    unfold deltaAt
    ring
  rw [e0]
  have hpos : 0 < 1 - 5 * (ε / 20) := by linarith
  rw [div_le_iff₀ hpos]
  nlinarith

/-- The answer to a #Knapsack instance `(S, C)`: query the output of the
divide-and-conquer algorithm at the capacity. -/
def approxCount (S : List ℕ) (C : ℕ) (ε : ℚ) : ℕ := queryLe (dc S ε) C

/-- **Theorem 1** (correctness): for `0 < ε ≤ 1`, the algorithm's answer
sandwiches the exact number `countLe S C` of subsets of `S` with total
weight at most `C`:

  `countLe S C ≤ approxCount S C ε ≤ (1+ε) · countLe S C`. -/
theorem approxCount_spec (S : List ℕ) (C : ℕ) (ε : ℚ) (h0 : 0 < ε) (h1 : ε ≤ 1) :
    countLe S C ≤ approxCount S C ε ∧
      (approxCount S C ε : ℚ) ≤ (1 + ε) * countLe S C := by
  obtain ⟨h, _⟩ := dc_spec S ε h0 h1
  unfold approxCount countLe
  rw [queryLe_spec]
  exact ⟨h.le C, h.ge C⟩
