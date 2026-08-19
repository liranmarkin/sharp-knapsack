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
import Mathlib

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

/-! ### D.2: a small hitting set exists (greedy, fully constructive)

Feng-Jin obtain their hitting set by the probabilistic method; the greedy
construction gives the same guarantee deterministically and is cleaner to
machine-check: each round some element hits an `s/n`-fraction of the still
unhit family, so `h` rounds leave at most `|F|·((n−s)/n)^h` unhit -
stated multiplicatively over ℕ. With `pow_shrink`, taking `h ≈ (n/s)·log`
rounds makes the unhit part an arbitrarily small fraction: the `Õ(n/ℓ)`
hitting set of Lemma 3.3. -/
theorem greedy_hitting (s : ℕ) :
    ∀ (h n : ℕ) (F : Finset (Finset ℕ)),
    (∀ X ∈ F, X ⊆ Finset.range n ∧ s ≤ X.card) →
    ∃ H : Finset ℕ, H.card ≤ h ∧
      ((F.filter (fun X => X ∩ H = ∅)).card) * n ^ h ≤ F.card * (n - s) ^ h := by
  intro h
  induction h with
  | zero =>
    intro n F _
    exact ⟨∅, by simp, by simp⟩
  | succ h ih =>
    intro n F hF
    by_cases hFne : F.Nonempty
    · by_cases hn : 0 < n
      · -- double counting: some element is in an s/n fraction of F
        have hdouble : s * F.card ≤
            ∑ e ∈ Finset.range n, (F.filter (fun X => e ∈ X)).card := by
          have hswap : (∑ e ∈ Finset.range n, (F.filter (fun X => e ∈ X)).card) =
              ∑ X ∈ F, ((Finset.range n).filter (fun e => e ∈ X)).card := by
            simp only [Finset.card_filter]
            rw [Finset.sum_comm]
          rw [hswap]
          have hcard : ∀ X ∈ F, s ≤ ((Finset.range n).filter (fun e => e ∈ X)).card := by
            intro X hX
            have hfe : (Finset.range n).filter (fun e => e ∈ X) = X := by
              apply Finset.ext
              intro e
              simp only [Finset.mem_filter]
              constructor
              · exact fun he => he.2
              · intro he
                exact ⟨(hF X hX).1 he, he⟩
            rw [hfe]
            exact (hF X hX).2
          calc s * F.card = ∑ _X ∈ F, s := by
                rw [Finset.sum_const, smul_eq_mul, mul_comm]
            _ ≤ ∑ X ∈ F, ((Finset.range n).filter (fun e => e ∈ X)).card :=
                Finset.sum_le_sum hcard
        have hexists : ∃ e ∈ Finset.range n,
            s * F.card ≤ n * (F.filter (fun X => e ∈ X)).card := by
          by_contra hcon
          push Not at hcon
          have hlt : ∀ e ∈ Finset.range n,
              n * (F.filter (fun X => e ∈ X)).card + 1 ≤ s * F.card := by
            intro e he
            have := hcon e he
            omega
          have hsumlt : n * ∑ e ∈ Finset.range n, (F.filter (fun X => e ∈ X)).card + n ≤
              n * (s * F.card) := by
            calc n * (∑ e ∈ Finset.range n, (F.filter (fun X => e ∈ X)).card) + n
                = ∑ e ∈ Finset.range n,
                    (n * (F.filter (fun X => e ∈ X)).card + 1) := by
                  rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const,
                    Finset.card_range, smul_eq_mul, mul_one]
              _ ≤ ∑ _e ∈ Finset.range n, s * F.card := Finset.sum_le_sum hlt
              _ = n * (s * F.card) := by
                  rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
          have := Nat.mul_le_mul_left n hdouble
          omega
        obtain ⟨e, he, hecount⟩ := hexists
        -- recurse on the family not hit by e
        set F' := F.filter (fun X => e ∉ X) with hF'
        have hF'sub : ∀ X ∈ F', X ⊆ Finset.range n ∧ s ≤ X.card := by
          intro X hX
          rw [hF', Finset.mem_filter] at hX
          exact hF X hX.1
        obtain ⟨H', hH'card, hH'⟩ := ih n F' hF'sub
        refine ⟨insert e H', ?_, ?_⟩
        · calc (insert e H').card ≤ H'.card + 1 := Finset.card_insert_le _ _
            _ ≤ h + 1 := by omega
        · -- unhit by (insert e H') ⊆ unhit-by-H' within F'
          have hsub : F.filter (fun X => X ∩ insert e H' = ∅) ⊆
              F'.filter (fun X => X ∩ H' = ∅) := by
            intro X hX
            rw [Finset.mem_filter] at hX
            have hnotin : e ∉ X := by
              intro hin
              have : e ∈ X ∩ insert e H' :=
                Finset.mem_inter.mpr ⟨hin, Finset.mem_insert_self _ _⟩
              rw [hX.2] at this
              exact absurd this (Finset.notMem_empty e)
            rw [Finset.mem_filter, hF', Finset.mem_filter]
            refine ⟨⟨hX.1, hnotin⟩, ?_⟩
            apply Finset.eq_empty_of_forall_notMem
            intro x hx
            rw [Finset.mem_inter] at hx
            have : x ∈ X ∩ insert e H' :=
              Finset.mem_inter.mpr ⟨hx.1, Finset.mem_insert_of_mem hx.2⟩
            rw [hX.2] at this
            exact absurd this (Finset.notMem_empty x)
          have hcards := Finset.card_le_card hsub
          -- |F'| · n ≤ |F| · (n − s)
          have hF'card : F'.card * n ≤ F.card * (n - s) := by
            have hsplit : (F.filter (fun X => e ∈ X)).card + F'.card = F.card := by
              rw [hF']
              exact Finset.card_filter_add_card_filter_not (s := F) (fun X => e ∈ X)
            have hs_le_n : s ≤ n := by
              obtain ⟨X, hX⟩ := hFne
              have h1 := (hF X hX).2
              have h2 : X.card ≤ n := by
                calc X.card ≤ (Finset.range n).card :=
                      Finset.card_le_card (hF X hX).1
                  _ = n := Finset.card_range n
              omega
            have e1 : F'.card * n + (F.filter (fun X => e ∈ X)).card * n =
                F.card * n := by
              rw [← Nat.add_mul, Nat.add_comm, hsplit]
            have e2 : s * F.card ≤ (F.filter (fun X => e ∈ X)).card * n := by
              calc s * F.card ≤ n * (F.filter (fun X => e ∈ X)).card := hecount
                _ = (F.filter (fun X => e ∈ X)).card * n := Nat.mul_comm _ _
            have e3 : F.card * (n - s) + F.card * s = F.card * n := by
              rw [← Nat.mul_add]
              congr 1
              omega
            have e4 : s * F.card = F.card * s := Nat.mul_comm _ _
            omega
          calc (F.filter (fun X => X ∩ insert e H' = ∅)).card * n ^ (h + 1)
              ≤ (F'.filter (fun X => X ∩ H' = ∅)).card * n ^ (h + 1) :=
                Nat.mul_le_mul_right _ hcards
            _ = ((F'.filter (fun X => X ∩ H' = ∅)).card * n ^ h) * n := by ring
            _ ≤ (F'.card * (n - s) ^ h) * n := Nat.mul_le_mul_right _ hH'
            _ = (F'.card * n) * (n - s) ^ h := by ring
            _ ≤ (F.card * (n - s)) * (n - s) ^ h :=
                Nat.mul_le_mul_right _ hF'card
            _ = F.card * (n - s) ^ (h + 1) := by ring
      · -- n = 0: all sets are ∅ with s = 0, or F is constrained trivially
        refine ⟨∅, by simp, ?_⟩
        have hn0 : n = 0 := by omega
        subst hn0
        simp [pow_succ]
    · refine ⟨∅, by simp, ?_⟩
      rw [Finset.not_nonempty_iff_eq_empty] at hFne
      subst hFne
      simp

/-- The shrink factor: after `m ≥ n/s` greedy rounds, the unhit family has
halved: `2·(n−s)^m ≤ n^m`. Iterating gives an arbitrarily small fraction. -/
theorem pow_shrink (n s m : ℕ) (hs : 0 < s) (hsn : s ≤ n) (hm : n ≤ s * m) :
    2 * (n - s) ^ m ≤ n ^ m := by
  by_cases hsn' : s = n
  · have hm1 : 1 ≤ m := by nlinarith
    have hz : n - s = 0 := by omega
    rw [hz]
    rcases Nat.exists_eq_add_of_le hm1 with ⟨m', rfl⟩
    rw [zero_pow (by omega : 1 + m' ≠ 0)]
    simp
  · have hlt : s < n := lt_of_le_of_ne hsn hsn'
    have hn : 0 < n := by omega
    -- cast to ℚ and use Bernoulli
    have key : (2 : ℚ) * ((n - s : ℕ) : ℚ) ^ m ≤ ((n : ℕ) : ℚ) ^ m := by
      have hd : (0:ℚ) < ((n - s : ℕ) : ℚ) ∨ ((n - s : ℕ) : ℚ) = 0 := by
        rcases Nat.eq_zero_or_pos (n - s) with h | h
        · right; exact_mod_cast h
        · left; exact_mod_cast h
      rcases hd with hd | hd
      · have hnq : (0:ℚ) < (n:ℚ) := by exact_mod_cast hn
        have hber : (1 : ℚ) + m * (s / (n - s : ℕ)) ≤ (1 + s / (n - s : ℕ)) ^ m := by
          have hx : (0:ℚ) ≤ (s : ℚ) / ((n - s : ℕ) : ℚ) := by positivity
          have := one_add_mul_le_pow (by linarith : (-2:ℚ) ≤ (s : ℚ) / ((n - s : ℕ) : ℚ)) m
          linarith [this]
        have hfrac : (1 : ℚ) + (s : ℚ) / ((n - s : ℕ) : ℚ) =
            ((n : ℕ) : ℚ) / ((n - s : ℕ) : ℚ) := by
          field_simp
          push_cast [Nat.cast_sub hsn]
          ring
        have htwo : (2 : ℚ) ≤ (1 : ℚ) + m * (s / (n - s : ℕ)) := by
          have h1 : (1 : ℚ) ≤ (m : ℚ) * (s : ℚ) / ((n - s : ℕ) : ℚ) := by
            rw [le_div_iff₀ hd]
            have hcast : ((n : ℕ) : ℚ) ≤ (m : ℚ) * (s : ℚ) := by
              have : (n : ℚ) ≤ ((s * m : ℕ) : ℚ) := by exact_mod_cast hm
              push_cast at this
              linarith
            have hns : ((n - s : ℕ) : ℚ) ≤ (n : ℚ) := by
              have : n - s ≤ n := Nat.sub_le _ _
              exact_mod_cast this
            linarith
          have h2 : (m : ℚ) * ((s : ℚ) / ((n - s : ℕ) : ℚ)) =
              (m : ℚ) * (s : ℚ) / ((n - s : ℕ) : ℚ) := by ring
          linarith [h2 ▸ h1]
        have hchain : (2 : ℚ) ≤ (((n : ℕ) : ℚ) / ((n - s : ℕ) : ℚ)) ^ m := by
          calc (2 : ℚ) ≤ (1 : ℚ) + m * (s / (n - s : ℕ)) := htwo
            _ ≤ (1 + s / (n - s : ℕ)) ^ m := hber
            _ = (((n : ℕ) : ℚ) / ((n - s : ℕ) : ℚ)) ^ m := by rw [hfrac]
        have hpos : (0:ℚ) < ((n - s : ℕ) : ℚ) ^ m := by positivity
        rw [div_pow] at hchain
        rw [le_div_iff₀ hpos] at hchain
        linarith
      · rw [hd]
        rcases Nat.eq_zero_or_pos m with hm0 | hm0
        · subst hm0
          nlinarith
        · rcases Nat.exists_eq_add_of_le hm0 with ⟨m', rfl⟩
          rw [zero_pow (by omega : Nat.succ 0 + m' ≠ 0), mul_zero]
          positivity
    have h2 : ((2 * (n - s) ^ m : ℕ) : ℚ) ≤ ((n ^ m : ℕ) : ℚ) := by
      push_cast
      exact key
    exact_mod_cast h2

/-! ### D.4: the d-band bound (Feng-Jin Lemma 3.2)

Every solution band `Ω_d = {X : T + (d−1)g < W_X ≤ T + d·g}` maps into
`Ω × {small item sets}` by peeling at most `d` large items, so
`|Ω_d| ≤ (Σ_{y≤d} C(n,y))·|Ω| ≤ d·n^d·|Ω|`. -/

/-- If everything light in total weighs at most `T`, any overweight subset
contains a `g`-large item. -/
theorem exists_large_item (n T g : ℕ) (W : ℕ → ℕ) (X : Finset ℕ)
    (hX : X ⊆ Finset.range n) (hbig : T < ∑ j ∈ X, W j)
    (hsmall : (∑ j ∈ (Finset.range n).filter (fun j => W j ≤ g), W j) ≤ T) :
    ∃ j ∈ X, g < W j := by
  by_contra hcon
  push Not at hcon
  have hsub : X ⊆ (Finset.range n).filter (fun j => W j ≤ g) := by
    intro j hj
    rw [Finset.mem_filter]
    exact ⟨hX hj, hcon j hj⟩
  have := Finset.sum_le_sum_of_subset (f := W) hsub
  omega

/-- Peeling: at most `d` large-item removals bring an overweight subset
(of excess ≤ d·g) down into the solution set. -/
theorem exists_peel (n T g : ℕ) (W : ℕ → ℕ)
    (hsmall : (∑ j ∈ (Finset.range n).filter (fun j => W j ≤ g), W j) ≤ T) :
    ∀ d (X : Finset ℕ), X ⊆ Finset.range n →
      T < ∑ j ∈ X, W j → (∑ j ∈ X, W j) ≤ T + d * g →
      ∃ Y, Y ⊆ X ∧ 1 ≤ Y.card ∧ Y.card ≤ d ∧ (∑ j ∈ X \ Y, W j) ≤ T := by
  intro d
  induction d with
  | zero =>
    intro X _ hbig hup
    omega
  | succ d ih =>
    intro X hX hbig hup
    obtain ⟨j, hjX, hjW⟩ := exists_large_item n T g W X hX hbig hsmall
    have herase : (∑ i ∈ X.erase j, W i) + W j = ∑ i ∈ X, W i :=
      Finset.sum_erase_add X W hjX
    by_cases hdone : (∑ i ∈ X.erase j, W i) ≤ T
    · refine ⟨{j}, ?_, by simp, by simp, ?_⟩
      · simpa using hjX
      · have hsd : X \ {j} = X.erase j := by
          ext x
          simp [Finset.mem_erase, and_comm]
        rw [hsd]
        exact hdone
    · push Not at hdone
      have hgg : (d + 1) * g = d * g + g := by ring
      have hup' : (∑ i ∈ X.erase j, W i) ≤ T + d * g := by omega
      obtain ⟨Y', hY'sub, hY'1, hY'd, hY'w⟩ :=
        ih (X.erase j) (Finset.Subset.trans (Finset.erase_subset _ _) hX) hdone hup'
      refine ⟨insert j Y', ?_, ?_, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx'
        · exact hjX
        · exact Finset.erase_subset _ _ (hY'sub hx')
      · calc 1 ≤ Y'.card := hY'1
          _ ≤ (insert j Y').card := Finset.card_le_card (Finset.subset_insert _ _)
      · calc (insert j Y').card ≤ Y'.card + 1 := Finset.card_insert_le _ _
          _ ≤ d + 1 := by omega
      · have hsd : X \ insert j Y' = (X.erase j) \ Y' := by
          ext x
          simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
          tauto
        rw [hsd]
        exact hY'w

/-- **The d-band bound** (Feng-Jin Lemma 3.2): the band of excess up to
`d·g` has size at most `(Σ_{1≤y≤d} C(n,y))·|Ω|`. -/
theorem band_d_le (n T g d : ℕ) (W : ℕ → ℕ)
    (hsmall : (∑ j ∈ (Finset.range n).filter (fun j => W j ≤ g), W j) ≤ T) :
    ((Finset.range n).powerset.filter
        (fun X => T < ∑ j ∈ X, W j ∧ (∑ j ∈ X, W j) ≤ T + d * g)).card ≤
      ((Finset.range n).powerset.filter
        (fun Y => 1 ≤ Y.card ∧ Y.card ≤ d)).card * (solSet n W T).card := by
  classical
  set B := (Finset.range n).powerset.filter
    (fun X => T < ∑ j ∈ X, W j ∧ (∑ j ∈ X, W j) ≤ T + d * g) with hB
  set YS := (Finset.range n).powerset.filter (fun Y => 1 ≤ Y.card ∧ Y.card ≤ d) with hYS
  let peel : Finset ℕ → Finset ℕ := fun X =>
    if h : X ⊆ Finset.range n ∧ T < ∑ j ∈ X, W j ∧ (∑ j ∈ X, W j) ≤ T + d * g then
      Classical.choose (exists_peel n T g W hsmall d X h.1 h.2.1 h.2.2)
    else ∅
  have hpeel : ∀ X ∈ B, peel X ⊆ X ∧ 1 ≤ (peel X).card ∧ (peel X).card ≤ d ∧
      (∑ j ∈ X \ peel X, W j) ≤ T := by
    intro X hX
    rw [hB, Finset.mem_filter, Finset.mem_powerset] at hX
    have hcond : X ⊆ Finset.range n ∧ T < ∑ j ∈ X, W j ∧
        (∑ j ∈ X, W j) ≤ T + d * g := ⟨hX.1, hX.2.1, hX.2.2⟩
    simp only [peel, dif_pos hcond]
    exact Classical.choose_spec (exists_peel n T g W hsmall d X hcond.1
      hcond.2.1 hcond.2.2)
  have hland : ∀ X ∈ B, (peel X, X \ peel X) ∈ YS ×ˢ solSet n W T := by
    intro X hX
    obtain ⟨hsub, h1, hd', hw⟩ := hpeel X hX
    rw [hB, Finset.mem_filter, Finset.mem_powerset] at hX
    rw [Finset.mem_product]
    constructor
    · rw [hYS, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.Subset.trans hsub hX.1, h1, hd'⟩
    · rw [solSet, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.Subset.trans Finset.sdiff_subset hX.1, hw⟩
  have hinj : ∀ X₁ ∈ B, ∀ X₂ ∈ B,
      (peel X₁, X₁ \ peel X₁) = (peel X₂, X₂ \ peel X₂) → X₁ = X₂ := by
    intro X₁ h₁ X₂ h₂ heq
    obtain ⟨hsub₁, -, -, -⟩ := hpeel X₁ h₁
    obtain ⟨hsub₂, -, -, -⟩ := hpeel X₂ h₂
    have e1 : peel X₁ = peel X₂ := (Prod.mk.injEq _ _ _ _).mp heq |>.1
    have e2 : X₁ \ peel X₁ = X₂ \ peel X₂ := (Prod.mk.injEq _ _ _ _).mp heq |>.2
    calc X₁ = (X₁ \ peel X₁) ∪ peel X₁ := (Finset.sdiff_union_of_subset hsub₁).symm
      _ = (X₂ \ peel X₂) ∪ peel X₂ := by rw [e2, e1]
      _ = X₂ := Finset.sdiff_union_of_subset hsub₂
  calc B.card ≤ (YS ×ˢ solSet n W T).card :=
        Finset.card_le_card_of_injOn (fun X => (peel X, X \ peel X)) hland hinj
    _ = YS.card * (solSet n W T).card := Finset.card_product _ _

/-- The small-set collection is at most `d·n^d` (crude but polylog-tight). -/
theorem small_sets_card_le (n d : ℕ) (hn : 0 < n) :
    ((Finset.range n).powerset.filter
      (fun Y => 1 ≤ Y.card ∧ Y.card ≤ d)).card ≤ d * n ^ d := by
  classical
  have hsub : (Finset.range n).powerset.filter (fun Y => 1 ≤ Y.card ∧ Y.card ≤ d) ⊆
      (Finset.Icc 1 d).biUnion (fun y => Finset.powersetCard y (Finset.range n)) := by
    intro Y hY
    rw [Finset.mem_filter, Finset.mem_powerset] at hY
    rw [Finset.mem_biUnion]
    exact ⟨Y.card, Finset.mem_Icc.mpr ⟨hY.2.1, hY.2.2⟩,
      Finset.mem_powersetCard.mpr ⟨hY.1, rfl⟩⟩
  calc ((Finset.range n).powerset.filter
      (fun Y => 1 ≤ Y.card ∧ Y.card ≤ d)).card
      ≤ ((Finset.Icc 1 d).biUnion
          (fun y => Finset.powersetCard y (Finset.range n))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ y ∈ Finset.Icc 1 d, (Finset.powersetCard y (Finset.range n)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _y ∈ Finset.Icc 1 d, n ^ d := by
        apply Finset.sum_le_sum
        intro y hy
        rw [Finset.mem_Icc] at hy
        rw [Finset.card_powersetCard, Finset.card_range]
        calc n.choose y ≤ n ^ y := Nat.choose_le_pow n y
          _ ≤ n ^ d := Nat.pow_le_pow_right hn hy.2
    _ ≤ d * n ^ d := by
        rw [Finset.sum_const, smul_eq_mul, Nat.card_Icc]
        have : d + 1 - 1 = d := by omega
        rw [this]

/-! ### D.5: bipartite double counting - the skeleton of Feng-Jin Lemma 3.4

Their Ω^△ bound compares minimum degree on one side with maximum degree on
the other side of a bipartite graph (Claims 3.5/3.6). The counting core: -/
theorem bipartite_double_count {α β : Type} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (E : α → β → Bool)
    (dA dB : ℕ)
    (hdA : ∀ a ∈ A, dA ≤ (B.filter (fun b => E a b)).card)
    (hdB : ∀ b ∈ B, (A.filter (fun a => E a b)).card ≤ dB) :
    A.card * dA ≤ B.card * dB := by
  have hedges : (∑ a ∈ A, (B.filter (fun b => E a b)).card) =
      ∑ b ∈ B, (A.filter (fun a => E a b)).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
  calc A.card * dA = ∑ _a ∈ A, dA := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ a ∈ A, (B.filter (fun b => E a b)).card := Finset.sum_le_sum hdA
    _ = ∑ b ∈ B, (A.filter (fun a => E a b)).card := hedges
    _ ≤ ∑ _b ∈ B, dB := Finset.sum_le_sum hdB
    _ = B.card * dB := by rw [Finset.sum_const, smul_eq_mul]

/-- The degree engine of Claim 3.5: adding the `2^|G|` subsets of a
disjoint pool to a base set produces `2^|G|` distinct sets. -/
theorem card_union_pool (base G : Finset ℕ) (hdisj : Disjoint base G) :
    (G.powerset.image (fun S => base ∪ S)).card = 2 ^ G.card := by
  classical
  rw [Finset.card_image_of_injOn, Finset.card_powerset]
  intro S₁ h₁ S₂ h₂ heq
  rw [Finset.mem_coe, Finset.mem_powerset] at h₁ h₂
  have key : ∀ S ⊆ G, (base ∪ S) ∩ G = S := by
    intro S hS
    ext x
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨hx1 | hx1, hx2⟩
      · exact absurd hx2 (Finset.disjoint_left.mp hdisj hx1)
      · exact hx1
    · intro hx
      exact ⟨Or.inr hx, hS hx⟩
  have heq' : base ∪ S₁ = base ∪ S₂ := heq
  calc S₁ = (base ∪ S₁) ∩ G := (key S₁ h₁).symm
    _ = (base ∪ S₂) ∩ G := by rw [heq']
    _ = S₂ := key S₂ h₂

/-- The choice engine of Claim 3.6: at most `m·n^m` subsets of `[n]` have
fewer than `m` elements (crude binomial-sum bound, polylog-tight). -/
theorem card_small_subsets_lt (n m : ℕ) (hn : 0 < n) :
    ((Finset.range n).powerset.filter (fun Y => Y.card < m)).card ≤ m * n ^ m := by
  classical
  have hsub : (Finset.range n).powerset.filter (fun Y => Y.card < m) ⊆
      (Finset.range m).biUnion (fun y => Finset.powersetCard y (Finset.range n)) := by
    intro Y hY
    rw [Finset.mem_filter, Finset.mem_powerset] at hY
    rw [Finset.mem_biUnion]
    exact ⟨Y.card, Finset.mem_range.mpr hY.2,
      Finset.mem_powersetCard.mpr ⟨hY.1, rfl⟩⟩
  calc ((Finset.range n).powerset.filter (fun Y => Y.card < m)).card
      ≤ ((Finset.range m).biUnion
          (fun y => Finset.powersetCard y (Finset.range n))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ y ∈ Finset.range m, (Finset.powersetCard y (Finset.range n)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _y ∈ Finset.range m, n ^ m := by
        apply Finset.sum_le_sum
        intro y hy
        rw [Finset.mem_range] at hy
        rw [Finset.card_powersetCard, Finset.card_range]
        calc n.choose y ≤ n ^ y := Nat.choose_le_pow n y
          _ ≤ n ^ m := Nat.pow_le_pow_right hn (by omega)
    _ = m * n ^ m := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- Claim 3.5's geometric core: a base set plus a disjoint pool that
jointly fit under the capacity contribute `2^|G|` distinct solutions
extending the base within the pool. -/
theorem pool_neighbors_card (n T : ℕ) (W : ℕ → ℕ) (B G : Finset ℕ)
    (hB : B ⊆ Finset.range n) (hG : G ⊆ Finset.range n) (hdisj : Disjoint B G)
    (hw : (∑ j ∈ B, W j) + (∑ j ∈ G, W j) ≤ T) :
    2 ^ G.card ≤
      ((solSet n W T).filter (fun X => B ⊆ X ∧ X \ B ⊆ G)).card := by
  classical
  have himg : G.powerset.image (fun S => B ∪ S) ⊆
      (solSet n W T).filter (fun X => B ⊆ X ∧ X \ B ⊆ G) := by
    intro X hX
    rw [Finset.mem_image] at hX
    obtain ⟨S, hS, rfl⟩ := hX
    rw [Finset.mem_powerset] at hS
    have hSd : Disjoint B S := Finset.disjoint_of_subset_right hS hdisj
    rw [Finset.mem_filter]
    refine ⟨?_, Finset.subset_union_left, ?_⟩
    · rw [solSet, Finset.mem_filter, Finset.mem_powerset]
      constructor
      · exact Finset.union_subset hB (Finset.Subset.trans hS hG)
      · rw [Finset.sum_union hSd]
        have hSsum : (∑ j ∈ S, W j) ≤ ∑ j ∈ G, W j :=
          Finset.sum_le_sum_of_subset hS
        omega
    · intro x hx
      rw [Finset.mem_sdiff, Finset.mem_union] at hx
      rcases hx.1 with h | h
      · exact absurd h hx.2
      · exact hS h
  calc 2 ^ G.card = (G.powerset.image (fun S => B ∪ S)).card :=
        (card_union_pool B G hdisj).symm
    _ ≤ ((solSet n W T).filter (fun X => B ⊆ X ∧ X \ B ⊆ G)).card :=
        Finset.card_le_card himg

/-- Claim 3.6's counting core: if every member of a family decomposes as
`(X \ R) ∪ H` with `R` from `P` and `H` from `Q`, the family has at most
`|P|·|Q|` members. -/
theorem fiber_card_le {α : Type} [DecidableEq α] (F : Finset (Finset α))
    (X : Finset α) (P Q : Finset (Finset α))
    (h : ∀ Y ∈ F, ∃ R ∈ P, ∃ H ∈ Q, Y = (X \ R) ∪ H) :
    F.card ≤ P.card * Q.card := by
  classical
  let pick : Finset α → Finset α × Finset α := fun Y =>
    if hY : ∃ R ∈ P, ∃ H ∈ Q, Y = (X \ R) ∪ H then
      (Classical.choose hY, Classical.choose (Classical.choose_spec hY).2)
    else (∅, ∅)
  have hspec : ∀ Y ∈ F, pick Y ∈ P ×ˢ Q ∧ Y = (X \ (pick Y).1) ∪ (pick Y).2 := by
    intro Y hY
    have hex := h Y hY
    simp only [pick, dif_pos hex]
    obtain ⟨hR, H, hH, hdec⟩ := Classical.choose_spec hex
    obtain ⟨hH', hdec'⟩ := Classical.choose_spec (Classical.choose_spec hex).2
    exact ⟨Finset.mem_product.mpr ⟨hR, hH'⟩, hdec'⟩
  calc F.card ≤ (P ×ˢ Q).card := by
        apply Finset.card_le_card_of_injOn pick (fun Y hY => (hspec Y hY).1)
        intro Y₁ h₁ Y₂ h₂ heq
        calc Y₁ = (X \ (pick Y₁).1) ∪ (pick Y₁).2 := (hspec Y₁ h₁).2
          _ = (X \ (pick Y₂).1) ∪ (pick Y₂).2 := by rw [heq]
          _ = Y₂ := ((hspec Y₂ h₂).2).symm
    _ = P.card * Q.card := Finset.card_product _ _

/-- Claim 3.5's weight arithmetic: stripping huge items (weight ≥ 40L²T/ℓ)
from a set with at most `m₁` large items leaves weight at most `9T/10`,
given the global light-item bound (their eq. (6)) and `100·m₁·L² ≤ ℓ`.
All thresholds are multiplicative. -/
theorem hat_weight_le (n T ℓ L2 m₁ : ℕ) (W : ℕ → ℕ) (X : Finset ℕ)
    (hX : X ⊆ Finset.range n) (hL2 : 0 < L2)
    (hsmall : 2 * (∑ j ∈ (Finset.range n).filter (fun j => W j * ℓ ≤ T), W j) ≤ T)
    (hfew : (X.filter (fun j => T < W j * ℓ)).card ≤ m₁)
    (hm₁ : 100 * m₁ * L2 ≤ ℓ) :
    10 * (∑ j ∈ X.filter (fun j => W j * ℓ < 40 * L2 * T), W j) ≤ 9 * T := by
  classical
  set Xh := X.filter (fun j => W j * ℓ < 40 * L2 * T) with hXh
  have hsplit : (∑ j ∈ Xh.filter (fun j => W j * ℓ ≤ T), W j) +
      ∑ j ∈ Xh.filter (fun j => ¬ W j * ℓ ≤ T), W j = ∑ j ∈ Xh, W j := by
    rw [Finset.sum_filter_add_sum_filter_not]
  have hlight : 2 * (∑ j ∈ Xh.filter (fun j => W j * ℓ ≤ T), W j) ≤ T := by
    have hsub : Xh.filter (fun j => W j * ℓ ≤ T) ⊆
        (Finset.range n).filter (fun j => W j * ℓ ≤ T) := by
      intro j hj
      rw [Finset.mem_filter] at hj
      have hjX : j ∈ X := by
        have h1 := hj.1
        rw [hXh, Finset.mem_filter] at h1
        exact h1.1
      rw [Finset.mem_filter]
      exact ⟨hX hjX, hj.2⟩
    have := Finset.sum_le_sum_of_subset (f := W) hsub
    omega
  have hmid : 100 * (∑ j ∈ Xh.filter (fun j => ¬ W j * ℓ ≤ T), W j) ≤ 40 * T := by
    have hcard : (Xh.filter (fun j => ¬ W j * ℓ ≤ T)).card ≤ m₁ := by
      have hsub : Xh.filter (fun j => ¬ W j * ℓ ≤ T) ⊆
          X.filter (fun j => T < W j * ℓ) := by
        intro j hj
        rw [Finset.mem_filter] at hj ⊢
        have h1 := hj.1
        rw [hXh, Finset.mem_filter] at h1
        exact ⟨h1.1, by omega⟩
      exact le_trans (Finset.card_le_card hsub) hfew
    have hsum : (∑ j ∈ Xh.filter (fun j => ¬ W j * ℓ ≤ T), W j) * ℓ ≤
        m₁ * (40 * L2 * T) := by
      rw [Finset.sum_mul]
      calc (∑ j ∈ Xh.filter (fun j => ¬ W j * ℓ ≤ T), W j * ℓ)
          ≤ ∑ _j ∈ Xh.filter (fun j => ¬ W j * ℓ ≤ T), 40 * L2 * T := by
            apply Finset.sum_le_sum
            intro j hj
            rw [Finset.mem_filter] at hj
            have h1 := hj.1
            rw [hXh, Finset.mem_filter] at h1
            omega
        _ = (Xh.filter (fun j => ¬ W j * ℓ ≤ T)).card * (40 * L2 * T) := by
            rw [Finset.sum_const, smul_eq_mul]
        _ ≤ m₁ * (40 * L2 * T) := Nat.mul_le_mul_right _ hcard
    rcases Nat.eq_zero_or_pos m₁ with hm0 | hm0
    · have hempty : Xh.filter (fun j => ¬ W j * ℓ ≤ T) = ∅ :=
        Finset.card_eq_zero.mp (by omega)
      rw [hempty]
      simp
    · have hpos : 0 < m₁ * L2 := Nat.mul_pos hm0 hL2
      have key : (m₁ * L2) * (100 * ∑ j ∈ Xh.filter (fun j => ¬ W j * ℓ ≤ T), W j) ≤
          (m₁ * L2) * (40 * T) := by
        calc (m₁ * L2) * (100 * ∑ j ∈ Xh.filter (fun j => ¬ W j * ℓ ≤ T), W j)
            = (∑ j ∈ Xh.filter (fun j => ¬ W j * ℓ ≤ T), W j) * (100 * m₁ * L2) := by
              ring
          _ ≤ (∑ j ∈ Xh.filter (fun j => ¬ W j * ℓ ≤ T), W j) * ℓ :=
              Nat.mul_le_mul_left _ hm₁
          _ ≤ m₁ * (40 * L2 * T) := hsum
          _ = (m₁ * L2) * (40 * T) := by ring
      exact Nat.le_of_mul_le_mul_left key hpos
  omega

/-- Claim 3.6's huge-count bound: a set of weight at most `2T` contains
few huge items - multiplicatively, `#huge · 40·L²·T ≤ 2·T·ℓ`. -/
theorem huge_count_le (T ℓ L2 : ℕ) (W : ℕ → ℕ) (Y : Finset ℕ)
    (hw : (∑ j ∈ Y, W j) ≤ 2 * T) :
    (Y.filter (fun j => 40 * L2 * T ≤ W j * ℓ)).card * (40 * L2 * T) ≤
      2 * T * ℓ := by
  classical
  calc (Y.filter (fun j => 40 * L2 * T ≤ W j * ℓ)).card * (40 * L2 * T)
      = ∑ _j ∈ Y.filter (fun j => 40 * L2 * T ≤ W j * ℓ), 40 * L2 * T := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ j ∈ Y.filter (fun j => 40 * L2 * T ≤ W j * ℓ), W j * ℓ := by
        apply Finset.sum_le_sum
        intro j hj
        exact (Finset.mem_filter.mp hj).2
    _ = (∑ j ∈ Y.filter (fun j => 40 * L2 * T ≤ W j * ℓ), W j) * ℓ := by
        rw [Finset.sum_mul]
    _ ≤ (∑ j ∈ Y, W j) * ℓ :=
        Nat.mul_le_mul_right _
          (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _))
    _ ≤ 2 * T * ℓ := Nat.mul_le_mul_right _ hw

/-- The good-item pool exists: if `Good` has `g₀ + m₁` members and at most
`m₁` of them meet `X`, a `g₀`-sized pool disjoint from `X` remains. -/
theorem pool_exists (m₁ g₀ : ℕ) (Good X : Finset ℕ)
    (hcard : g₀ + m₁ ≤ Good.card)
    (hfew : (Good ∩ X).card ≤ m₁) :
    ∃ G, G ⊆ Good ∧ G.card = g₀ ∧ Disjoint G X := by
  classical
  have hsplit : (Good \ X).card + (Good ∩ X).card = Good.card :=
    Finset.card_sdiff_add_card_inter Good X
  have hbig : g₀ ≤ (Good \ X).card := by omega
  obtain ⟨G, hGsub, hGcard⟩ := Finset.exists_subset_card_eq hbig
  refine ⟨G, Finset.Subset.trans hGsub Finset.sdiff_subset, hGcard, ?_⟩
  rw [Finset.disjoint_left]
  intro a haG haX
  exact (Finset.mem_sdiff.mp (hGsub haG)).2 haX

/-! ### D.10: Claims 3.5 and 3.6 assembled, and Lemma 3.4 -/

/-- **Claim 3.5**: every few-large-items set has at least `2^g₀` neighbor
solutions (extensions of its huge-free part by good items). -/
theorem claim_35 (n T ℓ L2 m₁ g₀ : ℕ) (W : ℕ → ℕ) (X : Finset ℕ)
    (hX : X ⊆ Finset.range n) (hL2 : 0 < L2)
    (hsmall : 2 * (∑ j ∈ (Finset.range n).filter (fun j => W j * ℓ ≤ T), W j) ≤ T)
    (hfew : (X.filter (fun j => T < W j * ℓ)).card ≤ m₁)
    (hm₁ : 100 * m₁ * L2 ≤ ℓ)
    (hg₀ : 20 * g₀ ≤ ℓ)
    (hGood : g₀ + m₁ ≤
      ((Finset.range n).filter (fun j => T < W j * ℓ ∧ W j * ℓ ≤ 2 * T)).card) :
    2 ^ g₀ ≤ ((solSet n W T).filter (fun Y =>
        X.filter (fun j => W j * ℓ < 40 * L2 * T) ⊆ Y ∧
        Y \ X.filter (fun j => W j * ℓ < 40 * L2 * T) ⊆
          (Finset.range n).filter
            (fun j => T < W j * ℓ ∧ W j * ℓ ≤ 2 * T))).card := by
  classical
  set Gd := (Finset.range n).filter (fun j => T < W j * ℓ ∧ W j * ℓ ≤ 2 * T)
    with hGd
  set Xh := X.filter (fun j => W j * ℓ < 40 * L2 * T) with hXh
  -- the pool
  have hmeet : (Gd ∩ X).card ≤ m₁ := by
    have hsub : Gd ∩ X ⊆ X.filter (fun j => T < W j * ℓ) := by
      intro j hj
      rw [Finset.mem_inter] at hj
      have h1 := hj.1
      rw [hGd, Finset.mem_filter] at h1
      rw [Finset.mem_filter]
      exact ⟨hj.2, h1.2.1⟩
    exact le_trans (Finset.card_le_card hsub) hfew
  obtain ⟨G, hGsub, hGcard, hGdisj⟩ := pool_exists m₁ g₀ Gd X hGood hmeet
  -- pool weight: 10·Σ_G ≤ T
  have hGw : 10 * (∑ j ∈ G, W j) ≤ T := by
    have h1 : (∑ j ∈ G, W j) * ℓ ≤ g₀ * (2 * T) := by
      rw [Finset.sum_mul]
      calc (∑ j ∈ G, W j * ℓ) ≤ ∑ _j ∈ G, 2 * T := by
            apply Finset.sum_le_sum
            intro j hj
            have := hGsub hj
            rw [hGd, Finset.mem_filter] at this
            exact this.2.2
        _ = G.card * (2 * T) := by rw [Finset.sum_const, smul_eq_mul]
        _ = g₀ * (2 * T) := by rw [hGcard]
    rcases Nat.eq_zero_or_pos g₀ with hg | hg
    · have hGe : G = ∅ := Finset.card_eq_zero.mp (by omega)
      rw [hGe]
      simp
    · have key : g₀ * (2 * (10 * ∑ j ∈ G, W j)) ≤ g₀ * (2 * T) := by
        calc g₀ * (2 * (10 * ∑ j ∈ G, W j))
            = (∑ j ∈ G, W j) * (20 * g₀) := by ring
          _ ≤ (∑ j ∈ G, W j) * ℓ := Nat.mul_le_mul_left _ hg₀
          _ ≤ g₀ * (2 * T) := h1
      have := Nat.le_of_mul_le_mul_left key hg
      omega
  -- the huge-free part fits with the pool under the capacity
  have hXhw := hat_weight_le n T ℓ L2 m₁ W X hX hL2 hsmall hfew hm₁
  have hcap : (∑ j ∈ Xh, W j) + (∑ j ∈ G, W j) ≤ T := by
    rw [← hXh] at hXhw
    omega
  -- disjointness and ranges
  have hXhsub : Xh ⊆ Finset.range n :=
    Finset.Subset.trans (Finset.filter_subset _ _) hX
  have hGrange : G ⊆ Finset.range n :=
    Finset.Subset.trans hGsub (Finset.filter_subset _ _)
  have hdisj : Disjoint Xh G := by
    apply Finset.disjoint_of_subset_left (Finset.filter_subset _ _)
    exact hGdisj.symm
  -- count via the pool, then relax G to the full good set
  calc 2 ^ g₀ = 2 ^ G.card := by rw [hGcard]
    _ ≤ ((solSet n W T).filter (fun Y => Xh ⊆ Y ∧ Y \ Xh ⊆ G)).card :=
        pool_neighbors_card n T W Xh G hXhsub hGrange hdisj hcap
    _ ≤ ((solSet n W T).filter (fun Y => Xh ⊆ Y ∧ Y \ Xh ⊆ Gd)).card := by
        apply Finset.card_le_card
        intro Y hY
        rw [Finset.mem_filter] at hY ⊢
        exact ⟨hY.1, hY.2.1, Finset.Subset.trans hY.2.2 hGsub⟩

/-- **Claim 3.6**: for a fixed solution `X`, at most
`((m₁+1)·n^(m₁+1))·((m₂+1)·n^(m₂+1))` few-large-items sets have `X` as a
neighbor. -/
theorem claim_36 (n T ℓ L2 m₁ m₂ : ℕ) (W : ℕ → ℕ) (X : Finset ℕ)
    (hn : 0 < n) (hT : 0 < T) (hL2 : 0 < L2)
    (hm₂ : 2 * ℓ ≤ m₂ * (40 * L2))
    (F : Finset (Finset ℕ))
    (hF : ∀ Y ∈ F, Y ⊆ Finset.range n ∧ (∑ j ∈ Y, W j) ≤ 2 * T ∧
      (Y.filter (fun j => T < W j * ℓ)).card ≤ m₁ ∧
      Y.filter (fun j => W j * ℓ < 40 * L2 * T) ⊆ X ∧
      X \ Y.filter (fun j => W j * ℓ < 40 * L2 * T) ⊆
        (Finset.range n).filter (fun j => T < W j * ℓ ∧ W j * ℓ ≤ 2 * T)) :
    F.card ≤ ((m₁ + 1) * n ^ (m₁ + 1)) * ((m₂ + 1) * n ^ (m₂ + 1)) := by
  classical
  set Gd := (Finset.range n).filter (fun j => T < W j * ℓ ∧ W j * ℓ ≤ 2 * T)
    with hGd
  set P := ((Finset.range n).powerset.filter (fun K => K.card < m₁ + 1)).image
    (fun K => Gd \ K) with hP
  set Q := (Finset.range n).powerset.filter (fun H => H.card < m₂ + 1) with hQ
  have hdec : ∀ Y ∈ F, ∃ R ∈ P, ∃ H ∈ Q, Y = (X \ R) ∪ H := by
    intro Y hY
    obtain ⟨hYr, hYw, hYfew, hhat, hgood⟩ := hF Y hY
    set Yh := Y.filter (fun j => W j * ℓ < 40 * L2 * T) with hYh
    set Hu := Y.filter (fun j => ¬ W j * ℓ < 40 * L2 * T) with hHu
    set K := Yh ∩ Gd with hK
    refine ⟨Gd \ K, ?_, Hu, ?_, ?_⟩
    · rw [hP, Finset.mem_image]
      refine ⟨K, ?_, rfl⟩
      rw [Finset.mem_filter, Finset.mem_powerset]
      constructor
      · calc K ⊆ Yh := Finset.inter_subset_left
          _ ⊆ Y := Finset.filter_subset _ _
          _ ⊆ Finset.range n := hYr
      · have hKsub : K ⊆ Y.filter (fun j => T < W j * ℓ) := by
          intro j hj
          rw [hK, Finset.mem_inter] at hj
          have h2 := hj.2
          rw [hGd, Finset.mem_filter] at h2
          rw [Finset.mem_filter]
          exact ⟨Finset.filter_subset _ _ hj.1, h2.2.1⟩
        have := Finset.card_le_card hKsub
        omega
    · rw [hQ, Finset.mem_filter, Finset.mem_powerset]
      constructor
      · exact Finset.Subset.trans (Finset.filter_subset _ _) hYr
      · have hcount := huge_count_le T ℓ L2 W Y hYw
        have hHuc : Hu.card * (40 * L2 * T) ≤ 2 * T * ℓ := by
          rw [hHu]
          have hiff : Y.filter (fun j => ¬ W j * ℓ < 40 * L2 * T) =
              Y.filter (fun j => 40 * L2 * T ≤ W j * ℓ) := by
            apply Finset.filter_congr
            intro j _
            exact not_lt
          rw [hiff]
          exact hcount
        by_contra hcon
        push Not at hcon
        have h1 : (m₂ + 1) * (40 * L2 * T) ≤ Hu.card * (40 * L2 * T) :=
          Nat.mul_le_mul_right _ (by omega)
        have h2 : 2 * T * ℓ = (2 * ℓ) * T := by ring
        have h3 : (2 * ℓ) * T ≤ (m₂ * (40 * L2)) * T :=
          Nat.mul_le_mul_right _ hm₂
        have h4 : (m₂ * (40 * L2)) * T = m₂ * (40 * L2 * T) := by ring
        have h5 : (m₂ + 1) * (40 * L2 * T) = m₂ * (40 * L2 * T) + 40 * L2 * T := by
          ring
        have hpos : 0 < 40 * L2 * T := by positivity
        omega
    · -- the decomposition identity Y = (X \ (Gd \ K)) ∪ Hu
      have hYsplit : Yh ∪ Hu = Y := by
        rw [hYh, hHu]
        exact Finset.filter_union_filter_not_eq _ Y
      have hhat' : X \ Gd ⊆ Yh := by
        intro x hx
        rw [Finset.mem_sdiff] at hx
        by_contra hxY
        exact hx.2 (hgood (Finset.mem_sdiff.mpr ⟨hx.1, hxY⟩))
      have hYheq : Yh = (X \ Gd) ∪ K := by
        apply Finset.Subset.antisymm
        · intro y hy
          rw [Finset.mem_union, Finset.mem_sdiff]
          by_cases hyGd : y ∈ Gd
          · right
            rw [hK, Finset.mem_inter]
            exact ⟨hy, hyGd⟩
          · left
            exact ⟨hhat hy, hyGd⟩
        · apply Finset.union_subset hhat'
          rw [hK]
          exact Finset.inter_subset_left
      have hKX : K ⊆ X := by
        rw [hK]
        exact Finset.Subset.trans Finset.inter_subset_left hhat
      have hXR : X \ (Gd \ K) = (X \ Gd) ∪ K := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_union]
        constructor
        · rintro ⟨hxX, hnot⟩
          by_cases hxGd : x ∈ Gd
          · right
            by_contra hxK
            exact hnot ⟨hxGd, hxK⟩
          · left
            exact ⟨hxX, hxGd⟩
        · rintro (⟨hxX, hxGd⟩ | hxK)
          · exact ⟨hxX, fun h => hxGd h.1⟩
          · exact ⟨hKX hxK, fun h => h.2 hxK⟩
      rw [hXR, ← hYheq]
      exact hYsplit.symm
  exact le_trans (fiber_card_le F X P Q hdec) (by
    have hPcard : P.card ≤ (m₁ + 1) * n ^ (m₁ + 1) := by
      calc P.card ≤ ((Finset.range n).powerset.filter
          (fun K => K.card < m₁ + 1)).card := Finset.card_image_le
        _ ≤ (m₁ + 1) * n ^ (m₁ + 1) := card_small_subsets_lt n (m₁ + 1) hn
    have hQcard : Q.card ≤ (m₂ + 1) * n ^ (m₂ + 1) :=
      card_small_subsets_lt n (m₂ + 1) hn
    exact Nat.mul_le_mul hPcard hQcard)

/-- **Feng-Jin Lemma 3.4** (parametrized): the family Ω^△ of `(T, 2T]`-
weight subsets with at most `m₁` large items is at most a 1/100-fraction
of the solution set, whenever the parameters satisfy the (paper's-choice)
inequalities - in particular the exponent gap
`100·((m₁+1)n^{m₁+1})·((m₂+1)n^{m₂+1}) ≤ 2^{g₀}`. -/
theorem lemma_34 (n T ℓ L2 m₁ m₂ g₀ : ℕ) (W : ℕ → ℕ)
    (hn : 0 < n) (hT : 0 < T) (hL2 : 0 < L2)
    (hsmall : 2 * (∑ j ∈ (Finset.range n).filter (fun j => W j * ℓ ≤ T), W j) ≤ T)
    (hm₁ : 100 * m₁ * L2 ≤ ℓ)
    (hg₀ : 20 * g₀ ≤ ℓ)
    (hGood : g₀ + m₁ ≤
      ((Finset.range n).filter (fun j => T < W j * ℓ ∧ W j * ℓ ≤ 2 * T)).card)
    (hm₂ : 2 * ℓ ≤ m₂ * (40 * L2))
    (hexp : 100 * (((m₁ + 1) * n ^ (m₁ + 1)) * ((m₂ + 1) * n ^ (m₂ + 1))) ≤ 2 ^ g₀) :
    100 * ((Finset.range n).powerset.filter (fun Y =>
        T < (∑ j ∈ Y, W j) ∧ (∑ j ∈ Y, W j) ≤ 2 * T ∧
        (Y.filter (fun j => T < W j * ℓ)).card ≤ m₁)).card ≤
      (solSet n W T).card := by
  classical
  set A := (Finset.range n).powerset.filter (fun Y =>
    T < (∑ j ∈ Y, W j) ∧ (∑ j ∈ Y, W j) ≤ 2 * T ∧
    (Y.filter (fun j => T < W j * ℓ)).card ≤ m₁) with hA
  set Gd := (Finset.range n).filter (fun j => T < W j * ℓ ∧ W j * ℓ ≤ 2 * T)
    with hGd
  set E : Finset ℕ → Finset ℕ → Bool := fun Y X =>
    decide (Y.filter (fun j => W j * ℓ < 40 * L2 * T) ⊆ X ∧
      X \ Y.filter (fun j => W j * ℓ < 40 * L2 * T) ⊆ Gd) with hE
  set dB := ((m₁ + 1) * n ^ (m₁ + 1)) * ((m₂ + 1) * n ^ (m₂ + 1)) with hdB
  have hdc := bipartite_double_count A (solSet n W T) E (2 ^ g₀) dB
    (by
      intro Y hY
      rw [hA, Finset.mem_filter, Finset.mem_powerset] at hY
      obtain ⟨hYr, -, -, hYfew⟩ := hY
      have h35 := claim_35 n T ℓ L2 m₁ g₀ W Y hYr hL2 hsmall hYfew hm₁ hg₀
        (by rw [← hGd] at *; exact hGood)
      calc 2 ^ g₀ ≤ ((solSet n W T).filter (fun X =>
            Y.filter (fun j => W j * ℓ < 40 * L2 * T) ⊆ X ∧
            X \ Y.filter (fun j => W j * ℓ < 40 * L2 * T) ⊆ Gd)).card := by
            rw [hGd]
            exact h35
        _ = ((solSet n W T).filter (fun X => E Y X)).card := by
            congr 1
            apply Finset.filter_congr
            intro X _
            rw [hE]
            simp
      )
    (by
      intro X hX
      have h36 := claim_36 n T ℓ L2 m₁ m₂ W X hn hT hL2 hm₂
        (A.filter (fun Y => E Y X))
        (by
          intro Y hY
          rw [Finset.mem_filter] at hY
          obtain ⟨hYA, hYE⟩ := hY
          rw [hA, Finset.mem_filter, Finset.mem_powerset] at hYA
          rw [hE] at hYE
          simp only [decide_eq_true_eq] at hYE
          rw [hGd] at hYE
          exact ⟨hYA.1, le_of_lt hYA.2.1 |>.trans (le_refl _) |> fun _ => hYA.2.2.1,
            hYA.2.2.2, hYE.1, hYE.2⟩)
      rw [← hdB] at h36
      exact h36)
  -- conclude: cancel dB
  have hdBpos : 0 < dB := by
    rw [hdB]
    positivity
  by_contra hcon
  push Not at hcon
  have h1 : (solSet n W T).card * dB < (100 * A.card) * dB :=
    (Nat.mul_lt_mul_right hdBpos).mpr hcon
  have h2 : (100 * A.card) * dB = A.card * (100 * dB) := by ring
  have h3 : A.card * (100 * dB) ≤ A.card * 2 ^ g₀ := by
    apply Nat.mul_le_mul_left
    calc 100 * dB = 100 * (((m₁ + 1) * n ^ (m₁ + 1)) * ((m₂ + 1) * n ^ (m₂ + 1))) := by
          rw [hdB]
      _ ≤ 2 ^ g₀ := hexp
  omega

/-- The exponent gap of Lemma 3.4, generically: whenever the linear
exponent inequality holds, the fiber bound is dominated by `2^g`. -/
theorem exponent_gap (L g m₁ m₂ n : ℕ) (hn : n ≤ 2 ^ L)
    (h : 7 + (m₁ + 1) * (L + 1) + (m₂ + 1) * (L + 1) ≤ g) :
    100 * (((m₁ + 1) * n ^ (m₁ + 1)) * ((m₂ + 1) * n ^ (m₂ + 1))) ≤ 2 ^ g := by
  have hfac : ∀ m : ℕ, (m + 1) * n ^ (m + 1) ≤ 2 ^ ((m + 1) * (L + 1)) := by
    intro m
    calc (m + 1) * n ^ (m + 1)
        ≤ 2 ^ (m + 1) * n ^ (m + 1) := by
          apply Nat.mul_le_mul_right
          exact le_of_lt (Nat.lt_two_pow_self)
      _ ≤ 2 ^ (m + 1) * (2 ^ L) ^ (m + 1) := by
          apply Nat.mul_le_mul_left
          exact Nat.pow_le_pow_left hn _
      _ = 2 ^ ((m + 1) * (L + 1)) := by
          rw [← pow_mul, ← pow_add]
          congr 1
          ring
  calc 100 * (((m₁ + 1) * n ^ (m₁ + 1)) * ((m₂ + 1) * n ^ (m₂ + 1)))
      ≤ 2 ^ 7 * (2 ^ ((m₁ + 1) * (L + 1)) * 2 ^ ((m₂ + 1) * (L + 1))) := by
        apply Nat.mul_le_mul (by norm_num)
        exact Nat.mul_le_mul (hfac m₁) (hfac m₂)
    _ = 2 ^ (7 + (m₁ + 1) * (L + 1) + (m₂ + 1) * (L + 1)) := by
        rw [← pow_add, ← pow_add]
        congr 1
        ring
    _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) h

/-- The parameter choice of Lemma 3.4: with `m₁ = ℓ/(100L²)`,
`m₂ = ℓ/(20L²) + 1`, `g₀ = ℓ/(10L)`, the linear exponent inequality of
`exponent_gap` holds whenever `ℓ ≥ 4000·L²`. -/
theorem params_choice (ℓ L : ℕ) (hL : 2 ≤ L) (hℓ : 4000 * L ^ 2 ≤ ℓ) :
    7 + (ℓ / (100 * L ^ 2) + 1) * (L + 1) +
      ((ℓ / (20 * L ^ 2) + 1) + 1) * (L + 1) ≤ ℓ / (10 * L) := by
  set a := ℓ / (100 * L ^ 2) with ha
  set b := ℓ / (20 * L ^ 2) with hb
  set g := ℓ / (10 * L) with hg
  have hLpos : 0 < L := by omega
  -- division facts, atom-aligned
  have fa : 100 * (a * L ^ 2) ≤ ℓ := by
    have h := Nat.div_mul_le_self ℓ (100 * L ^ 2)
    rw [← ha] at h
    have e : a * (100 * L ^ 2) = 100 * (a * L ^ 2) := by ring
    omega
  have fb : 20 * (b * L ^ 2) ≤ ℓ := by
    have h := Nat.div_mul_le_self ℓ (20 * L ^ 2)
    rw [← hb] at h
    have e : b * (20 * L ^ 2) = 20 * (b * L ^ 2) := by ring
    omega
  have hdm := Nat.div_add_mod ℓ (10 * L)
  have hmod : ℓ % (10 * L) < 10 * L := Nat.mod_lt ℓ (by positivity)
  have fg : 10 * (g * L) + ℓ % (10 * L) = ℓ := by
    rw [← hg] at hdm
    have e : (10 * L) * g = 10 * (g * L) := by ring
    omega
  -- small-atom relations from L ≥ 2
  have r3 : 2 * (a * L) ≤ a * L ^ 2 := by
    have h := Nat.mul_le_mul_left (a * L) hL
    have e : a * L * L = a * L ^ 2 := by ring
    omega
  have r4 : 2 * (b * L) ≤ b * L ^ 2 := by
    have h := Nat.mul_le_mul_left (b * L) hL
    have e : b * L * L = b * L ^ 2 := by ring
    omega
  have r5 : 2 * L ≤ L ^ 2 := by
    have h := Nat.mul_le_mul_left L hL
    have e : L * L = L ^ 2 := by ring
    omega
  -- reduce to the 200L-multiplied inequality and cancel
  have hmain : (7 + (a + 1) * (L + 1) + (b + 1 + 1) * (L + 1)) * (200 * L) ≤
      g * (200 * L) := by
    have e1 : (7 + (a + 1) * (L + 1) + (b + 1 + 1) * (L + 1)) * (200 * L) =
        200 * (a * L ^ 2) + 200 * (b * L ^ 2) + 200 * (a * L) + 200 * (b * L) +
          600 * L ^ 2 + 2000 * L := by ring
    have e2 : g * (200 * L) = 20 * (10 * (g * L)) := by ring
    omega
  exact Nat.le_of_mul_le_mul_right hmain (by positivity)

/-! ### D.12: Lemma 3.3 - the sample-complexity bound assembled -/

/-- Core-restricted greedy hitting: hit only within each member's `core`
(⊆ a universe `U`), with the shrink factor over `|U|`. -/
theorem greedy_hitting_core (s : ℕ) (U : Finset ℕ) :
    ∀ (h : ℕ) (F : Finset (Finset ℕ)) (core : Finset ℕ → Finset ℕ),
    (∀ X ∈ F, core X ⊆ U ∧ s ≤ (core X).card) →
    ∃ H : Finset ℕ, H ⊆ U ∧ H.card ≤ h ∧
      ((F.filter (fun X => core X ∩ H = ∅)).card) * U.card ^ h ≤
        F.card * (U.card - s) ^ h := by
  intro h
  induction h with
  | zero =>
    intro F core _
    exact ⟨∅, Finset.empty_subset _, by simp, by simp⟩
  | succ h ih =>
    intro F core hF
    rcases Nat.eq_zero_or_pos s with hs | hs
    · refine ⟨∅, Finset.empty_subset _, by simp, ?_⟩
      subst hs
      simp only [Nat.sub_zero]
      exact Nat.mul_le_mul_right _
        (Finset.card_le_card (Finset.filter_subset _ _))
    by_cases hFne : F.Nonempty
    · have hUne : 0 < U.card := by
        obtain ⟨X, hX⟩ := hFne
        obtain ⟨hsub, hcard⟩ := hF X hX
        have h1 : 0 < (core X).card := by omega
        calc 0 < (core X).card := h1
          _ ≤ U.card := Finset.card_le_card hsub
      have hdouble : s * F.card ≤
          ∑ e ∈ U, (F.filter (fun X => e ∈ core X)).card := by
        have hswap : (∑ e ∈ U, (F.filter (fun X => e ∈ core X)).card) =
            ∑ X ∈ F, (U.filter (fun e => e ∈ core X)).card := by
          simp only [Finset.card_filter]
          rw [Finset.sum_comm]
        rw [hswap]
        have hcard : ∀ X ∈ F, s ≤ (U.filter (fun e => e ∈ core X)).card := by
          intro X hX
          obtain ⟨hsub, hcard⟩ := hF X hX
          have hfe : U.filter (fun e => e ∈ core X) = core X := by
            apply Finset.ext
            intro e
            simp only [Finset.mem_filter]
            exact ⟨fun he => he.2, fun he => ⟨hsub he, he⟩⟩
          rw [hfe]
          exact hcard
        calc s * F.card = ∑ _X ∈ F, s := by
              rw [Finset.sum_const, smul_eq_mul, mul_comm]
          _ ≤ ∑ X ∈ F, (U.filter (fun e => e ∈ core X)).card :=
              Finset.sum_le_sum hcard
      have hexists : ∃ e ∈ U,
          s * F.card ≤ U.card * (F.filter (fun X => e ∈ core X)).card := by
        by_contra hcon
        push Not at hcon
        have hlt : ∀ e ∈ U,
            U.card * (F.filter (fun X => e ∈ core X)).card + 1 ≤ s * F.card := by
          intro e he
          have := hcon e he
          omega
        have hsumlt : U.card * (∑ e ∈ U, (F.filter (fun X => e ∈ core X)).card)
            + U.card ≤ U.card * (s * F.card) := by
          calc U.card * (∑ e ∈ U, (F.filter (fun X => e ∈ core X)).card) + U.card
              = ∑ e ∈ U, (U.card * (F.filter (fun X => e ∈ core X)).card + 1) := by
                rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const,
                  smul_eq_mul, mul_one]
            _ ≤ ∑ _e ∈ U, s * F.card := Finset.sum_le_sum hlt
            _ = U.card * (s * F.card) := by
                rw [Finset.sum_const, smul_eq_mul]
        have := Nat.mul_le_mul_left U.card hdouble
        omega
      obtain ⟨e, he, hecount⟩ := hexists
      set F' := F.filter (fun X => e ∉ core X) with hF'
      have hF'sub : ∀ X ∈ F', core X ⊆ U ∧ s ≤ (core X).card := by
        intro X hX
        rw [hF', Finset.mem_filter] at hX
        exact hF X hX.1
      obtain ⟨H', hH'U, hH'card, hH'⟩ := ih F' core hF'sub
      refine ⟨insert e H', Finset.insert_subset he hH'U, ?_, ?_⟩
      · calc (insert e H').card ≤ H'.card + 1 := Finset.card_insert_le _ _
          _ ≤ h + 1 := by omega
      · have hsub : F.filter (fun X => core X ∩ insert e H' = ∅) ⊆
            F'.filter (fun X => core X ∩ H' = ∅) := by
          intro X hX
          rw [Finset.mem_filter] at hX
          have hnotin : e ∉ core X := by
            intro hin
            have : e ∈ core X ∩ insert e H' :=
              Finset.mem_inter.mpr ⟨hin, Finset.mem_insert_self _ _⟩
            rw [hX.2] at this
            exact absurd this (Finset.notMem_empty e)
          rw [Finset.mem_filter, hF', Finset.mem_filter]
          refine ⟨⟨hX.1, hnotin⟩, ?_⟩
          apply Finset.eq_empty_of_forall_notMem
          intro x hx
          rw [Finset.mem_inter] at hx
          have : x ∈ core X ∩ insert e H' :=
            Finset.mem_inter.mpr ⟨hx.1, Finset.mem_insert_of_mem hx.2⟩
          rw [hX.2] at this
          exact absurd this (Finset.notMem_empty x)
        have hcards := Finset.card_le_card hsub
        have hF'card : F'.card * U.card ≤ F.card * (U.card - s) := by
          have hsplit : (F.filter (fun X => e ∈ core X)).card + F'.card = F.card := by
            rw [hF']
            exact Finset.card_filter_add_card_filter_not (s := F) _
          have hs_le : s ≤ U.card := by
            obtain ⟨X, hX⟩ := hFne
            obtain ⟨hsub', hcard'⟩ := hF X hX
            calc s ≤ (core X).card := hcard'
              _ ≤ U.card := Finset.card_le_card hsub'
          have e1 : F'.card * U.card + (F.filter (fun X => e ∈ core X)).card * U.card =
              F.card * U.card := by
            rw [← Nat.add_mul, Nat.add_comm, hsplit]
          have e2 : s * F.card ≤ (F.filter (fun X => e ∈ core X)).card * U.card := by
            calc s * F.card ≤ U.card * (F.filter (fun X => e ∈ core X)).card :=
                  hecount
              _ = (F.filter (fun X => e ∈ core X)).card * U.card := Nat.mul_comm _ _
          have e3 : F.card * (U.card - s) + F.card * s = F.card * U.card := by
            rw [← Nat.mul_add]
            congr 1
            omega
          have e4 : s * F.card = F.card * s := Nat.mul_comm _ _
          omega
        calc (F.filter (fun X => core X ∩ insert e H' = ∅)).card * U.card ^ (h + 1)
            ≤ (F'.filter (fun X => core X ∩ H' = ∅)).card * U.card ^ (h + 1) :=
              Nat.mul_le_mul_right _ hcards
          _ = ((F'.filter (fun X => core X ∩ H' = ∅)).card * U.card ^ h) * U.card := by
              ring
          _ ≤ (F'.card * (U.card - s) ^ h) * U.card := Nat.mul_le_mul_right _ hH'
          _ = (F'.card * U.card) * (U.card - s) ^ h := by ring
          _ ≤ (F.card * (U.card - s)) * (U.card - s) ^ h :=
              Nat.mul_le_mul_right _ hF'card
          _ = F.card * (U.card - s) ^ (h + 1) := by ring
    · refine ⟨∅, Finset.empty_subset _, by simp, ?_⟩
      rw [Finset.not_nonempty_iff_eq_empty] at hFne
      subst hFne
      simp

/-- The mapping bound with `H`-local weights: it suffices that the
*hitting-set members* exceed the gap. -/
theorem band_hit_le' (n T g : ℕ) (W : ℕ → ℕ) (H : Finset ℕ)
    (hw : ∀ i ∈ H, g < W i) :
    ((bandSet n W T g).filter (fun X => (X ∩ H).Nonempty)).card ≤
      H.card * (solSet n W T).card := by
  classical
  set B := (bandSet n W T g).filter (fun X => (X ∩ H).Nonempty) with hB
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
    have h2 : X₁.erase (pick X₁) = X₂.erase (pick X₂) :=
      (Prod.mk.injEq _ _ _ _).mp heq |>.2
    calc X₁ = insert (pick X₁) (X₁.erase (pick X₁)) := (Finset.insert_erase hp₁.1).symm
      _ = insert (pick X₂) (X₂.erase (pick X₂)) := by rw [h2, h1]
      _ = X₂ := Finset.insert_erase hp₂.1
  have hland : ∀ X ∈ B, (pick X, X.erase (pick X)) ∈ H ×ˢ solSet n W T := by
    intro X hX
    have hp := hpick X hX
    rw [Finset.mem_inter] at hp
    rw [hB, Finset.mem_filter] at hX
    have hband := hX.1
    rw [bandSet, Finset.mem_filter, Finset.mem_powerset] at hband
    obtain ⟨hsub, -, hup⟩ := hband
    rw [Finset.mem_product]
    refine ⟨hp.2, ?_⟩
    rw [solSet, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.Subset.trans (Finset.erase_subset _ _) hsub, ?_⟩
    have hWx : g < W (pick X) := hw _ hp.2
    have hsum : (∑ i ∈ X.erase (pick X), W i) + W (pick X) = ∑ i ∈ X, W i :=
      Finset.sum_erase_add X W hp.1
    show (∑ i ∈ X.erase (pick X), W i) ≤ T
    omega
  calc B.card ≤ (H ×ˢ solSet n W T).card :=
        Finset.card_le_card_of_injOn (fun X => (pick X, X.erase (pick X)))
          hland hinj
    _ = H.card * (solSet n W T).card := Finset.card_product _ _

/-- **Feng-Jin Lemma 3.3** (parametrized): the boundary band `Ω₁` is at
most a `(1 + 200h)/100`-fraction of the solution set - the sample
complexity of the whole algorithm. Composed from Lemma 3.4 (few-large-item
members), the core-restricted greedy hitting set, and the deletion
mapping (many-large-item members). -/
theorem lemma_33 (n T ℓ L2 m₁ m₂ g₀ h gap : ℕ) (W : ℕ → ℕ)
    (hn : 0 < n) (hT : 0 < T) (hL2 : 0 < L2) (_hℓ : 0 < ℓ) (hm₁pos : 1 ≤ m₁)
    (hsmall : 2 * (∑ j ∈ (Finset.range n).filter (fun j => W j * ℓ ≤ T), W j) ≤ T)
    (hm₁ : 100 * m₁ * L2 ≤ ℓ)
    (hg₀ : 20 * g₀ ≤ ℓ)
    (hGood : g₀ + m₁ ≤
      ((Finset.range n).filter (fun j => T < W j * ℓ ∧ W j * ℓ ≤ 2 * T)).card)
    (hm₂ : 2 * ℓ ≤ m₂ * (40 * L2))
    (hexp : 100 * (((m₁ + 1) * n ^ (m₁ + 1)) * ((m₂ + 1) * n ^ (m₂ + 1))) ≤ 2 ^ g₀)
    (hgap : gap * ℓ ≤ T) (hgapT : gap ≤ T)
    (hhit : 2 * (((Finset.range n).filter (fun j => T < W j * ℓ)).card - m₁) ^ h ≤
      ((Finset.range n).filter (fun j => T < W j * ℓ)).card ^ h) :
    100 * (bandSet n W T gap).card ≤ (1 + 200 * h) * (solSet n W T).card := by
  classical
  set U := (Finset.range n).filter (fun j => T < W j * ℓ) with hU
  set Ω₁ := bandSet n W T gap with hΩ₁
  set core : Finset ℕ → Finset ℕ := fun X => X.filter (fun j => T < W j * ℓ)
    with hcore
  have hsplitΩ : (Ω₁.filter (fun X => (core X).card ≤ m₁)).card +
      (Ω₁.filter (fun X => ¬ (core X).card ≤ m₁)).card = Ω₁.card :=
    Finset.card_filter_add_card_filter_not (s := Ω₁) _
  -- few-large part: inside Lemma 3.4's family
  have h34 := lemma_34 n T ℓ L2 m₁ m₂ g₀ W hn hT hL2 hsmall hm₁ hg₀ hGood hm₂ hexp
  have hA1card : 100 * (Ω₁.filter (fun X => (core X).card ≤ m₁)).card ≤
      (solSet n W T).card := by
    refine le_trans (Nat.mul_le_mul_left 100 (Finset.card_le_card ?_)) h34
    intro X hX
    rw [Finset.mem_filter] at hX
    obtain ⟨hXΩ, hXcard⟩ := hX
    rw [hΩ₁, bandSet, Finset.mem_filter, Finset.mem_powerset] at hXΩ
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hXΩ.1, hXΩ.2.1, by omega, hXcard⟩
  -- many-large part
  set F := Ω₁.filter (fun X => ¬ (core X).card ≤ m₁) with hFdef
  have hFcore : ∀ X ∈ F, core X ⊆ U ∧ m₁ ≤ (core X).card := by
    intro X hX
    rw [hFdef, Finset.mem_filter] at hX
    obtain ⟨hXΩ, hXcard⟩ := hX
    rw [hΩ₁, bandSet, Finset.mem_filter, Finset.mem_powerset] at hXΩ
    constructor
    · intro j hj
      rw [hcore, Finset.mem_filter] at hj
      rw [hU, Finset.mem_filter]
      exact ⟨hXΩ.1 hj.1, hj.2⟩
    · omega
  obtain ⟨H, hHU, hHcard, hHbound⟩ := greedy_hitting_core m₁ U h F core hFcore
  by_cases hFne : F.Nonempty
  · have hUpos : 0 < U.card := by
      obtain ⟨X, hX⟩ := hFne
      obtain ⟨hsub, hcard⟩ := hFcore X hX
      calc 0 < (core X).card := by omega
        _ ≤ U.card := Finset.card_le_card hsub
    have hUpow : 0 < U.card ^ h := pow_pos hUpos h
    have hunhit2 : 2 * (F.filter (fun X => core X ∩ H = ∅)).card ≤ F.card := by
      have k1 : (2 * (F.filter (fun X => core X ∩ H = ∅)).card) * U.card ^ h ≤
          F.card * U.card ^ h := by
        calc (2 * (F.filter (fun X => core X ∩ H = ∅)).card) * U.card ^ h
            = 2 * ((F.filter (fun X => core X ∩ H = ∅)).card * U.card ^ h) := by
              ring
          _ ≤ 2 * (F.card * (U.card - m₁) ^ h) :=
              Nat.mul_le_mul_left 2 hHbound
          _ = F.card * (2 * (U.card - m₁) ^ h) := by ring
          _ ≤ F.card * U.card ^ h := Nat.mul_le_mul_left _ hhit
      exact Nat.le_of_mul_le_mul_right k1 hUpow
    have hhitsplit : (F.filter (fun X => core X ∩ H = ∅)).card +
        (F.filter (fun X => ¬ core X ∩ H = ∅)).card = F.card :=
      Finset.card_filter_add_card_filter_not (s := F) _
    have hhitcard : (F.filter (fun X => ¬ core X ∩ H = ∅)).card ≤
        h * (solSet n W T).card := by
      have hmap : F.filter (fun X => ¬ core X ∩ H = ∅) ⊆
          (bandSet n W T gap).filter (fun X => (X ∩ H).Nonempty) := by
        intro X hX
        rw [Finset.mem_filter] at hX
        obtain ⟨hXF, hXhit⟩ := hX
        rw [hFdef, Finset.mem_filter] at hXF
        rw [Finset.mem_filter]
        refine ⟨by rw [← hΩ₁]; exact hXF.1, ?_⟩
        have hne : (core X ∩ H).Nonempty :=
          Finset.nonempty_iff_ne_empty.mpr hXhit
        obtain ⟨x, hx⟩ := hne
        rw [Finset.mem_inter] at hx
        exact ⟨x, Finset.mem_inter.mpr
          ⟨Finset.filter_subset _ _ hx.1, hx.2⟩⟩
      have hw : ∀ i ∈ H, gap < W i := by
        intro i hi
        have := hHU hi
        rw [hU, Finset.mem_filter] at this
        have hgapℓ : gap * ℓ < W i * ℓ := by omega
        exact Nat.lt_of_mul_lt_mul_right hgapℓ
      calc (F.filter (fun X => ¬ core X ∩ H = ∅)).card
          ≤ ((bandSet n W T gap).filter (fun X => (X ∩ H).Nonempty)).card :=
            Finset.card_le_card hmap
        _ ≤ H.card * (solSet n W T).card := band_hit_le' n T gap W H hw
        _ ≤ h * (solSet n W T).card :=
            Nat.mul_le_mul_right _ hHcard
    -- combine
    have hF2 : F.card ≤ 2 * (h * (solSet n W T).card) := by omega
    have hrhs : (1 + 200 * h) * (solSet n W T).card =
        (solSet n W T).card + 200 * (h * (solSet n W T).card) := by ring
    omega
  · rw [Finset.not_nonempty_iff_eq_empty] at hFne
    have hF0 : F.card = 0 := by rw [hFne]; simp
    have hΩeq : Ω₁.card = (Ω₁.filter (fun X => (core X).card ≤ m₁)).card := by
      omega
    calc 100 * Ω₁.card = 100 * (Ω₁.filter (fun X => (core X).card ≤ m₁)).card := by
          rw [hΩeq]
      _ ≤ (solSet n W T).card := hA1card
      _ ≤ (1 + 200 * h) * (solSet n W T).card :=
          Nat.le_mul_of_pos_left _ (by omega)
