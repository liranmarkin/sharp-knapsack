/-
# Stage F.1a: the merge layer - one step of the fast construction

The fast construction builds each node's array from its children via the
witness machinery (Feng-Jin §6.2). This file verifies the *correctness* of
one merge, reducing Stage F to a purely computational oracle:

* `convQ` - the exact rational convolution of the children's arrays;
* `WitnessOracle` - the postcondition of their Theorem 6.1: per position,
  the returned value is exactly the attaining-diagonal mass (by Stage 0's
  `witness_product_identity`, this is what `D^C·w` aggregates);
* `merge_dominates` - via `diagonal_witness_domination`, the oracle's
  array is pointwise within `[convQ/(1+δ), convQ]` of the exact
  convolution of the children.

After this file, what remains of Stage F is only *implementing* the
oracle fast (their Theorem 6.1 / BDP24: FFT + random primes) with its
cost model.
-/
import SharpKnapsack.New.SamplerArrays
import SharpKnapsack.New.WitnessSampler
import SharpKnapsack.FengJin.Oracle

open Finset

/-- **The merge dominates** (single-merge instance of Stage 0's diagonal
domination): with 3-divisible level sums and the level sandwiches, the
oracle's array is pointwise within `[convQ/(1+δ), convQ]`. -/
theorem merge_dominates (D δ : ℚ) (r : ℤ) (hD : 1 < D) (hδ : 0 < δ)
    (f g : ℕ → ℚ) (lv lw : ℕ → ℤ) (h : ℕ → ℚ)
    (hor : WitnessOracle f g lv lw h)
    (hnn : ∀ y, 0 ≤ f y) (hnn' : ∀ z, 0 ≤ g z)
    (hlvf : ∀ y, f y ≠ 0 → D ^ lv y ≤ f y ∧ f y < D ^ (lv y + 1))
    (hlwg : ∀ z, g z ≠ 0 → D ^ lw z ≤ g z ∧ g z < D ^ (lw z + 1))
    (hsep3 : ∀ y z : ℕ, f y ≠ 0 → g z ≠ 0 → (lv y + lw z) % 3 = r)
    (s : ℕ) (hs : (s + 1 : ℚ) ≤ δ * D) :
    h s ≤ convQ f g s ∧ convQ f g s ≤ (1 + δ) * h s := by
  classical
  obtain ⟨C, hub, hatt, hval⟩ := hor s
  have hnneg : ∀ y ∈ range (s + 1), 0 ≤ f y * g (s - y) :=
    fun y _ => mul_nonneg (hnn y) (hnn' (s - y))
  by_cases hzero : convQ f g s = 0
  · have hall : ∀ y ∈ range (s + 1), f y * g (s - y) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hnneg).mp hzero
    have hh0 : h s = 0 := by
      rw [hval]
      apply Finset.sum_eq_zero
      intro y hy
      exact hall y (Finset.mem_filter.mp hy).1
    rw [hh0, hzero]
    norm_num
  · set P := (range (s + 1)).filter (fun y => f y * g (s - y) ≠ 0) with hP
    have hPsub : P ⊆ range (s + 1) := Finset.filter_subset _ _
    -- restrict the oracle sum and the convolution to the support
    have hhP : h s = ∑ y ∈ P with lv y + lw (s - y) = C, f y * g (s - y) := by
      rw [hval]
      symm
      apply Finset.sum_subset
      · intro y hy
        rw [Finset.mem_filter] at hy ⊢
        rw [hP, Finset.mem_filter] at hy
        exact ⟨hy.1.1, hy.2⟩
      · intro y hy hyn
        by_contra h0
        apply hyn
        rw [Finset.mem_filter] at hy ⊢
        rw [hP, Finset.mem_filter]
        exact ⟨⟨hy.1, h0⟩, hy.2⟩
    have hconvP : convQ f g s = ∑ y ∈ P, f y * g (s - y) := by
      rw [convQ]
      symm
      apply Finset.sum_subset hPsub
      intro y hy hyn
      by_contra h0
      exact hyn (by rw [hP, Finset.mem_filter]; exact ⟨hy, h0⟩)
    have hsplit : (∑ y ∈ P, f y * g (s - y)) =
        (∑ y ∈ P with lv y + lw (s - y) = C, f y * g (s - y)) +
        ∑ y ∈ P with lv y + lw (s - y) ≠ C, f y * g (s - y) :=
      (Finset.sum_filter_add_sum_filter_not P _ _).symm
    -- domination via Stage 0
    have hdom := SharpKnapsack.diagonal_witness_domination s P hPsub
      (fun y => f y * g (s - y)) (fun y => lv y + lw (s - y)) D δ C hD hδ
      (by
        intro y hy
        rw [hP, Finset.mem_filter] at hy
        have hf : f y ≠ 0 := fun h0 => hy.2 (by rw [h0, zero_mul])
        have hg : g (s - y) ≠ 0 := fun h0 => hy.2 (by rw [h0, mul_zero])
        have h1 := (hlvf y hf).1
        have h2 := (hlwg (s - y) hg).1
        calc D ^ (lv y + lw (s - y)) = D ^ lv y * D ^ lw (s - y) :=
              zpow_add₀ (by positivity) _ _
          _ ≤ f y * g (s - y) := by
              apply mul_le_mul h1 h2 (by positivity) (hnn y))
      (by
        intro y hy
        rw [hP, Finset.mem_filter] at hy
        have hf : f y ≠ 0 := fun h0 => hy.2 (by rw [h0, zero_mul])
        have hg : g (s - y) ≠ 0 := fun h0 => hy.2 (by rw [h0, mul_zero])
        have h1 := (hlvf y hf).2
        have h2 := (hlwg (s - y) hg).2
        calc f y * g (s - y) < D ^ (lv y + 1) * D ^ (lw (s - y) + 1) := by
              apply mul_lt_mul'' h1 h2 (hnn y) (hnn' (s - y))
          _ = D ^ (lv y + lw (s - y) + 2) := by
              rw [← zpow_add₀ (by positivity : D ≠ 0)]
              congr 1
              ring)
      (by
        intro y hy
        rw [hP, Finset.mem_filter] at hy
        have hle := hub y hy.1 hy.2
        rcases eq_or_lt_of_le hle with heq | hlt
        · exact Or.inl heq
        · right
          have hfy : f y ≠ 0 := fun h0 => hy.2 (by rw [h0, zero_mul])
          have hgy : g (s - y) ≠ 0 := fun h0 => hy.2 (by rw [h0, mul_zero])
          have hd1 := hsep3 y (s - y) hfy hgy
          obtain ⟨y₀, hy₀, hy₀ne, hy₀C⟩ := hatt hzero
          have hf₀ : f y₀ ≠ 0 := fun h0 => hy₀ne (by rw [h0, zero_mul])
          have hg₀ : g (s - y₀) ≠ 0 := fun h0 => hy₀ne (by rw [h0, mul_zero])
          have hd2 : C % 3 = r := hy₀C ▸ hsep3 y₀ (s - y₀) hf₀ hg₀
          omega)
      (by
        obtain ⟨y₀, hy₀, hy₀ne, hy₀C⟩ := hatt hzero
        exact ⟨y₀, by rw [hP, Finset.mem_filter]; exact ⟨hy₀, hy₀ne⟩, hy₀C⟩)
      hs
    -- assemble the two bounds
    have hAttnn : 0 ≤ ∑ y ∈ P with lv y + lw (s - y) = C, f y * g (s - y) :=
      Finset.sum_nonneg fun y hy => hnneg y (hPsub (Finset.mem_filter.mp hy).1)
    have hNonnn : 0 ≤ ∑ y ∈ P with lv y + lw (s - y) ≠ C, f y * g (s - y) :=
      Finset.sum_nonneg fun y hy => hnneg y (hPsub (Finset.mem_filter.mp hy).1)
    constructor
    · rw [hhP, hconvP, hsplit]
      linarith
    · rw [hhP, hconvP, hsplit]
      linarith

/-- Convolution compounds pointwise sandwiches multiplicatively. -/
theorem convQ_sandwich (f g cf cg : ℕ → ℚ) (δ₁ δ₂ : ℚ)
    (hδ₁ : 0 ≤ δ₁) (_hδ₂ : 0 ≤ δ₂) (_hδ₁1 : δ₁ ≤ 1) (hδ₂1 : δ₂ ≤ 1)
    (hcf : ∀ y, 0 ≤ cf y) (hcg : ∀ z, 0 ≤ cg z)
    (hfnn : ∀ y, 0 ≤ f y) (hgnn : ∀ z, 0 ≤ g z)
    (hf : ∀ y, (1 - δ₁) * cf y ≤ f y ∧ f y ≤ (1 + δ₁) * cf y)
    (hg : ∀ z, (1 - δ₂) * cg z ≤ g z ∧ g z ≤ (1 + δ₂) * cg z)
    (s : ℕ) :
    (1 - δ₁) * (1 - δ₂) * convQ cf cg s ≤ convQ f g s ∧
      convQ f g s ≤ (1 + δ₁) * (1 + δ₂) * convQ cf cg s := by
  constructor
  · rw [convQ, convQ, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro y _
    calc (1 - δ₁) * (1 - δ₂) * (cf y * cg (s - y))
        = ((1 - δ₁) * cf y) * ((1 - δ₂) * cg (s - y)) := by ring
      _ ≤ f y * g (s - y) := by
          apply mul_le_mul (hf y).1 (hg (s - y)).1
          · exact mul_nonneg (by linarith) (hcg _)
          · exact hfnn y
  · rw [convQ, convQ, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro y _
    calc f y * g (s - y)
        ≤ ((1 + δ₁) * cf y) * ((1 + δ₂) * cg (s - y)) := by
          apply mul_le_mul (hf y).2 (hg (s - y)).2 (hgnn _)
          exact mul_nonneg (by linarith) (hcf _)
      _ = (1 + δ₁) * (1 + δ₂) * (cf y * cg (s - y)) := by ring

/-- **The merge induction step, assembled**: children within pointwise
`(1±δᵢ)` of reference arrays, plus a witness oracle, give a parent within
`[(1−δ₁)(1−δ₂)/(1+δ), (1+δ₁)(1+δ₂)]` of the exact convolution of the
references - the multiplicative form of the compounding `δ`-budget. -/
theorem merge_spec (D δ δ₁ δ₂ : ℚ) (r : ℤ) (hD : 1 < D) (hδ : 0 < δ)
    (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂) (hδ₁1 : δ₁ ≤ 1) (hδ₂1 : δ₂ ≤ 1)
    (f g cf cg : ℕ → ℚ) (lv lw : ℕ → ℤ) (h : ℕ → ℚ)
    (hor : WitnessOracle f g lv lw h)
    (hnn : ∀ y, 0 ≤ f y) (hnn' : ∀ z, 0 ≤ g z)
    (hcf : ∀ y, 0 ≤ cf y) (hcg : ∀ z, 0 ≤ cg z)
    (hf : ∀ y, (1 - δ₁) * cf y ≤ f y ∧ f y ≤ (1 + δ₁) * cf y)
    (hg : ∀ z, (1 - δ₂) * cg z ≤ g z ∧ g z ≤ (1 + δ₂) * cg z)
    (hlvf : ∀ y, f y ≠ 0 → D ^ lv y ≤ f y ∧ f y < D ^ (lv y + 1))
    (hlwg : ∀ z, g z ≠ 0 → D ^ lw z ≤ g z ∧ g z < D ^ (lw z + 1))
    (hsep3 : ∀ y z : ℕ, f y ≠ 0 → g z ≠ 0 → (lv y + lw z) % 3 = r)
    (s : ℕ) (hs : (s + 1 : ℚ) ≤ δ * D) :
    (1 - δ₁) * (1 - δ₂) * convQ cf cg s ≤ (1 + δ) * h s ∧
      h s ≤ (1 + δ₁) * (1 + δ₂) * convQ cf cg s := by
  obtain ⟨hdom1, hdom2⟩ := merge_dominates D δ r hD hδ f g lv lw h hor hnn hnn'
    hlvf hlwg hsep3 s hs
  obtain ⟨hs1, hs2⟩ := convQ_sandwich f g cf cg δ₁ δ₂ hδ₁ hδ₂ hδ₁1 hδ₂1
    hcf hcg hnn hnn' hf hg s
  exact ⟨le_trans hs1 hdom2, le_trans hdom1 hs2⟩

/-! ### The oracle is inhabited: a verified (slow) implementation

The fast implementation (FFT + random primes) is Stage F.1b; this
executable one meets the same spec, so every interface of the pipeline is
inhabited by verified code and only the *speed* claim remains open. -/

/-- The support of a diagonal. -/
def diagSupport (f g : ℕ → ℚ) (s : ℕ) : Finset ℕ :=
  (range (s + 1)).filter (fun y => f y * g (s - y) ≠ 0)

/-- The maximal supported level sum (0 on an empty diagonal). -/
def slowC (f g : ℕ → ℚ) (lv lw : ℕ → ℤ) (s : ℕ) : ℤ :=
  if h : (diagSupport f g s).Nonempty then
    ((diagSupport f g s).image (fun y => lv y + lw (s - y))).max'
      (h.image (fun y => lv y + lw (s - y)))
  else 0

/-- The attaining-diagonal mass at the maximal level. -/
def slowOracle (f g : ℕ → ℚ) (lv lw : ℕ → ℤ) (s : ℕ) : ℚ :=
  ∑ y ∈ (range (s + 1)).filter
      (fun y => lv y + lw (s - y) = slowC f g lv lw s),
    f y * g (s - y)

theorem slowOracle_spec (f g : ℕ → ℚ) (lv lw : ℕ → ℤ) :
    WitnessOracle f g lv lw (slowOracle f g lv lw) := by
  classical
  intro s
  refine ⟨slowC f g lv lw s, ?_, ?_, rfl⟩
  · intro y hy hne
    have hmem : y ∈ diagSupport f g s := by
      rw [diagSupport, Finset.mem_filter]
      exact ⟨hy, hne⟩
    have hne' : (diagSupport f g s).Nonempty := ⟨y, hmem⟩
    rw [slowC, dif_pos hne']
    exact Finset.le_max' _ _
      (Finset.mem_image_of_mem (fun y => lv y + lw (s - y)) hmem)
  · intro hconv
    have hne' : (diagSupport f g s).Nonempty := by
      by_contra hcon
      apply hconv
      rw [Finset.not_nonempty_iff_eq_empty, diagSupport] at hcon
      rw [convQ]
      apply Finset.sum_eq_zero
      intro y hy
      by_contra h0
      have : y ∈ (range (s + 1)).filter (fun y => f y * g (s - y) ≠ 0) :=
        Finset.mem_filter.mpr ⟨hy, h0⟩
      rw [hcon] at this
      exact absurd this (Finset.notMem_empty y)
    rw [slowC, dif_pos hne']
    have hmax := Finset.max'_mem
      ((diagSupport f g s).image (fun y => lv y + lw (s - y)))
      (hne'.image (fun y => lv y + lw (s - y)))
    rw [Finset.mem_image] at hmax
    obtain ⟨y₀, hy₀, hy₀eq⟩ := hmax
    rw [diagSupport, Finset.mem_filter] at hy₀
    exact ⟨y₀, hy₀.1, hy₀.2, hy₀eq⟩

