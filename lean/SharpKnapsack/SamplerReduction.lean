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
