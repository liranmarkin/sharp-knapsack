/-
# Stage D of the witness-sampler verification: the sample-complexity
# reduction (Feng-Jin Lemma 3.3, deterministic core)

The FPRAS needs only `Õ(n/ℓ)·ε⁻²` samples because the boundary band
`Ω₁ = {X : T < W_X ≤ T + T/ℓ}` is small relative to the solution set
`Ω = {X : W_X ≤ T}`. The deterministic heart of their argument (§1.2.6):

* `band_card_gt` - in the bounded-ratio regime every band subset has more
  than `ℓ/2` items (so a random `Õ(n/ℓ)`-sized set hits it);
* `band_hit_le` - the mapping bound: deleting one hit item sends the band
  injectively into `Ω × H`, so the `H`-hit part of the band has
  cardinality at most `|H| · |Ω|`.

The probabilistic-method existence of a good `H` (their `1 − o(1)`
coverage) is Stage D.2 on the roadmap.
-/
import SharpKnapsack.SamplerExact

open Finset

/-- Solutions of the instance: subsets of `range n` with weight at most `T`. -/
def solSet (n : ℕ) (W : ℕ → ℕ) (T : ℕ) : Finset (Finset ℕ) :=
  (Finset.range n).powerset.filter (fun X => ∑ i ∈ X, W i ≤ T)

/-- The boundary band `Ω₁`: weight in `(T, T + g]` for the gap `g = T/ℓ`. -/
def bandSet (n : ℕ) (W : ℕ → ℕ) (T g : ℕ) : Finset (Finset ℕ) :=
  (Finset.range n).powerset.filter
    (fun X => T < ∑ i ∈ X, W i ∧ ∑ i ∈ X, W i ≤ T + g)

/-- **Band subsets are large** (bounded-ratio regime): if every item weight
satisfies `W i · ℓ ≤ 2T`, a subset of weight above `T` has more than `ℓ/2`
items. This is what makes a small random set hit the whole band. -/
theorem band_card_gt (n : ℕ) (W : ℕ → ℕ) (T g ℓ : ℕ)
    (hw : ∀ i ∈ Finset.range n, W i * ℓ ≤ 2 * T)
    (X : Finset ℕ) (hX : X ∈ bandSet n W T g) :
    ℓ < 2 * X.card := by
  rw [bandSet, Finset.mem_filter, Finset.mem_powerset] at hX
  obtain ⟨hsub, hlow, -⟩ := hX
  have hsum : (∑ i ∈ X, W i) * ℓ ≤ X.card * (2 * T) := by
    rw [Finset.sum_mul]
    calc (∑ i ∈ X, W i * ℓ) ≤ ∑ _i ∈ X, 2 * T :=
          Finset.sum_le_sum fun i hi => hw i (hsub hi)
      _ = X.card * (2 * T) := by rw [Finset.sum_const, smul_eq_mul]
  by_contra hcon
  have h2 : 2 * X.card ≤ ℓ := by omega
  have hcard0 : 0 < X.card := by
    by_contra hc0
    have hX0 : X = ∅ := Finset.card_eq_zero.mp (by omega)
    rw [hX0] at hlow
    simp at hlow
  have h3 : (∑ i ∈ X, W i) * (2 * X.card) ≤ (∑ i ∈ X, W i) * ℓ :=
    Nat.mul_le_mul_left _ h2
  have h4 : T * (2 * X.card) < (∑ i ∈ X, W i) * (2 * X.card) :=
    (Nat.mul_lt_mul_right (by omega)).mpr hlow
  have h5 : X.card * (2 * T) = T * (2 * X.card) := by ring
  omega

/-- **The mapping bound** (deterministic core of Feng-Jin Lemma 3.3):
if every item weight exceeds the gap `g`, then deleting the smallest
`H`-item of a band subset lands in the solution set, injectively into
`Ω × H`. Hence the `H`-hit part of the band has size at most `|H| · |Ω|`. -/
theorem band_hit_le (n : ℕ) (W : ℕ → ℕ) (T g : ℕ) (H : Finset ℕ)
    (hw : ∀ i ∈ Finset.range n, g < W i) :
    ((bandSet n W T g).filter (fun X => (X ∩ H).Nonempty)).card ≤
      H.card * (solSet n W T).card := by
  classical
  set B := (bandSet n W T g).filter (fun X => (X ∩ H).Nonempty) with hB
  -- the injection X ↦ (removed item, the rest)
  let pick : Finset ℕ → ℕ := fun X =>
    if h : (X ∩ H).Nonempty then (X ∩ H).min' h else 0
  have hpick : ∀ X ∈ B, pick X ∈ X ∩ H := by
    intro X hX
    rw [hB, Finset.mem_filter] at hX
    simp only [pick, dif_pos hX.2]
    exact Finset.min'_mem _ _
  have hinj : ∀ X₁ ∈ B, ∀ X₂ ∈ B,
      (pick X₁, X₁.erase (pick X₁)) = (pick X₂, X₂.erase (pick X₂)) → X₁ = X₂ := by
    intro X₁ h₁ X₂ h₂ heq
    have hp₁ := hpick X₁ h₁
    have hp₂ := hpick X₂ h₂
    rw [Finset.mem_inter] at hp₁ hp₂
    have h1 : pick X₁ = pick X₂ := (Prod.mk.injEq _ _ _ _).mp heq |>.1
    have h2 : X₁.erase (pick X₁) = X₂.erase (pick X₂) := (Prod.mk.injEq _ _ _ _).mp heq |>.2
    calc X₁ = insert (pick X₁) (X₁.erase (pick X₁)) := (Finset.insert_erase hp₁.1).symm
      _ = insert (pick X₂) (X₂.erase (pick X₂)) := by rw [h2, h1]
      _ = X₂ := Finset.insert_erase hp₂.1
  -- the image lands in H ×ˢ Ω
  have hland : ∀ X ∈ B, (pick X, X.erase (pick X)) ∈ H ×ˢ solSet n W T := by
    intro X hX
    have hp := hpick X hX
    rw [Finset.mem_inter] at hp
    rw [hB, Finset.mem_filter] at hX
    have hband := hX.1
    rw [bandSet, Finset.mem_filter, Finset.mem_powerset] at hband
    obtain ⟨hsub, -, hup⟩ := hband
    rw [Finset.mem_product]
    constructor
    · exact hp.2
    · rw [solSet, Finset.mem_filter, Finset.mem_powerset]
      constructor
      · exact Finset.Subset.trans (Finset.erase_subset _ _) hsub
      · -- removing an item of weight > g brings the weight to ≤ T
        have hWx : g < W (pick X) := hw _ (hsub hp.1)
        have hsum : (∑ i ∈ X.erase (pick X), W i) + W (pick X) = ∑ i ∈ X, W i :=
          Finset.sum_erase_add X W hp.1
        show (∑ i ∈ X.erase (pick X), W i) ≤ T
        omega
  -- count through the injection
  calc B.card ≤ (H ×ˢ solSet n W T).card :=
        Finset.card_le_card_of_injOn (fun X => (pick X, X.erase (pick X)))
          hland hinj
    _ = H.card * (solSet n W T).card := Finset.card_product _ _
