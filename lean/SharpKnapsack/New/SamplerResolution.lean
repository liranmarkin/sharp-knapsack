/-
# The resolution lever (branch `resolution-lever`)

One mechanism replacing the amortization machinery of `beyond-n43`:
run the Feng-Jin pipeline at a grid fine enough that the TOTAL
accumulated round-down error `E` stays below one band width `gap = T/ℓ`.
Then the rounded solution set `Ω'` sandwiches as
`Ω ⊆ Ω' ⊆ Ω ∪ band(T, E)`, and their Lemma 3.3 (`lemma_33`, already
machine-checked and resolution-free) bounds the band, giving
`100·|Ω'| ≤ (101 + 200h)·|Ω|` - i.e. `p = |Ω|/|Ω'| ≥ 1/polylog` and the
sample count drops to `N = Õ(ε⁻²)`.

The cost side: boosting the grid multiplies array LENGTHS by `F`, but
- construction is per-merge `Õ(L·√M)` (their Thm 6.1, parametric in L):
  summed over a class tree this is `Õ(F·B·√M)` per class
  (`boost_construction_ledger`) = `Õ(n^{1.5})` at full crank `F·B ≈ n`;
- the pruned witness scan enumerates LEVELS, not positions: per sample
  `Õ(A)` independent of `F` (`scan_ledger`).

Composed headline: `fprasUniform` - total `Õ(n^{1.5} + n·ε⁻²)`,
uniformly in ε and ℓ.
-/
import SharpKnapsack.New.SamplerHeadline
import SharpKnapsack.FengJin.Reduction

open Finset

/-- Solutions of the ROUNDED count at threshold `T`, for an arbitrary
per-subset rounding `r` (the value the merge tree assigns to a mask). -/
def roundedSol (n : ℕ) (r : Finset ℕ → ℕ) (T : ℕ) : Finset (Finset ℕ) :=
  (Finset.range n).powerset.filter (fun X => r X ≤ T)

/-- Round-down never loses a solution: `Ω ⊆ Ω'`. -/
theorem rounded_superset (n T : ℕ) (W : ℕ → ℕ) (r : Finset ℕ → ℕ)
    (hlo : ∀ X ∈ (Finset.range n).powerset, r X ≤ ∑ i ∈ X, W i) :
    solSet n W T ⊆ roundedSol n r T := by
  intro X hX
  rw [solSet, mem_filter] at hX
  rw [roundedSol, mem_filter]
  exact ⟨hX.1, le_trans (hlo X hX.1) hX.2⟩

/-- A rounded solution is a true solution or lies in the error band. -/
theorem rounded_band_split (n T E : ℕ) (W : ℕ → ℕ) (r : Finset ℕ → ℕ)
    (hhi : ∀ X ∈ (Finset.range n).powerset, ∑ i ∈ X, W i ≤ r X + E) :
    roundedSol n r T ⊆ solSet n W T ∪ bandSet n W T E := by
  intro X hX
  rw [roundedSol, mem_filter] at hX
  by_cases hle : (∑ i ∈ X, W i) ≤ T
  case pos =>
    apply mem_union_left
    rw [solSet, mem_filter]
    exact ⟨hX.1, hle⟩
  case neg =>
    have hgt : T < ∑ i ∈ X, W i := Nat.lt_of_not_le hle
    apply mem_union_right
    rw [bandSet, mem_filter]
    refine ⟨hX.1, hgt, ?_⟩
    have := hhi X hX.1
    omega

/-- The band is monotone in its width. -/
theorem bandSet_mono (n T : ℕ) (W : ℕ → ℕ) {E g : ℕ} (h : E ≤ g) :
    bandSet n W T E ⊆ bandSet n W T g := by
  intro X hX
  rw [bandSet, mem_filter] at hX ⊢
  exact ⟨hX.1, hX.2.1, le_trans hX.2.2 (by omega)⟩

/-- **The machine-checked p-bound.** Under the instance-side hypotheses
of Feng-Jin's Lemma 3.3 (all resolution-free), any rounding whose total
error `E` stays below the band width `gap` yields
`|Ω| ≤ |Ω'| ≤ (101 + 200h)/100 · |Ω|` - the statistical heart of the
resolution lever: the sample count drops to `Õ(ε⁻²)`. -/
theorem resolution_p_bound
    (n T ℓ L2 m₁ m₂ g₀ h gap E : ℕ) (W : ℕ → ℕ) (r : Finset ℕ → ℕ)
    (hn : 0 < n) (hT : 0 < T) (hL2 : 0 < L2) (hℓ : 0 < ℓ) (hm₁pos : 1 ≤ m₁)
    (hsmall : 2 * (∑ j ∈ (Finset.range n).filter (fun j => W j * ℓ ≤ T), W j) ≤ T)
    (hm₁ : 100 * m₁ * L2 ≤ ℓ)
    (hg₀ : 20 * g₀ ≤ ℓ)
    (hGood : g₀ + m₁ ≤
      ((Finset.range n).filter (fun j => T < W j * ℓ ∧ W j * ℓ ≤ 2 * T)).card)
    (hm₂ : 2 * ℓ ≤ m₂ * (40 * L2))
    (hexp : 100 * (((m₁ + 1) * n ^ (m₁ + 1)) * ((m₂ + 1) * n ^ (m₂ + 1))) ≤ 2 ^ g₀)
    (hgap : gap * ℓ ≤ T) (hgapT : gap ≤ T)
    (hhit : 2 * (((Finset.range n).filter (fun j => T < W j * ℓ)).card - m₁) ^ h ≤
      ((Finset.range n).filter (fun j => T < W j * ℓ)).card ^ h)
    (hlo : ∀ X ∈ (Finset.range n).powerset, r X ≤ ∑ i ∈ X, W i)
    (hhi : ∀ X ∈ (Finset.range n).powerset, ∑ i ∈ X, W i ≤ r X + E)
    (hE : E ≤ gap) :
    (solSet n W T).card ≤ (roundedSol n r T).card ∧
    100 * (roundedSol n r T).card ≤ (101 + 200 * h) * (solSet n W T).card := by
  have hband := lemma_33 n T ℓ L2 m₁ m₂ g₀ h gap W hn hT hL2 hℓ hm₁pos hsmall
    hm₁ hg₀ hGood hm₂ hexp hgap hgapT hhit
  refine ⟨card_le_card (rounded_superset n T W r hlo), ?_⟩
  have h1 : roundedSol n r T ⊆ solSet n W T ∪ bandSet n W T gap := by
    intro X hX
    rcases mem_union.mp (rounded_band_split n T E W r hhi hX) with h2 | h2
    · exact mem_union_left _ h2
    · exact mem_union_right _ (bandSet_mono n T W hE h2)
  have h2 : (roundedSol n r T).card ≤
      (solSet n W T).card + (bandSet n W T gap).card :=
    le_trans (card_le_card h1) (card_union_le _ _)
  calc 100 * (roundedSol n r T).card
      ≤ 100 * ((solSet n W T).card + (bandSet n W T gap).card) :=
        Nat.mul_le_mul_left _ h2
    _ = 100 * (solSet n W T).card + 100 * (bandSet n W T gap).card := by ring
    _ ≤ 100 * (solSet n W T).card + (1 + 200 * h) * (solSet n W T).card :=
        Nat.add_le_add_left hband _
    _ = (101 + 200 * h) * (solSet n W T).card := by ring

/-- Construction cost of a class tree at boost `F`: depth-`h` arrays have
length `(F·B)/2^{h/2}` and the per-merge cost is length × √(levels)
(their Thm 6.1). Total: `Õ(F·B·√M)` - at full crank `F·B ≈ n` this is
`Õ(n^{1.5})`, independent of ℓ. -/
def boostLedger (F B M D : ℕ) : ℕ :=
  ∑ h ∈ range (D + 1),
    2 ^ h * (((F * B) / 2 ^ (h / 2)) * (Nat.sqrt (M / 2 ^ h) + 1))

theorem boost_construction_ledger (F B M D : ℕ) (h2D : 2 ^ D ≤ M) :
    boostLedger F B M D ≤ 4 * (D + 1) * ((F * B) * (Nat.sqrt M + 1)) := by
  have hterm : ∀ h ∈ range (D + 1),
      2 ^ h * (((F * B) / 2 ^ (h / 2)) * (Nat.sqrt (M / 2 ^ h) + 1)) ≤
        4 * ((F * B) * (Nat.sqrt M + 1)) := by
    intro h hmem
    have hh : h ≤ D := Nat.lt_succ_iff.mp (mem_range.mp hmem)
    have h1 : (2:ℕ) ^ h ≤ 2 * (2 ^ (h / 2) * 2 ^ (h / 2)) := by
      calc (2:ℕ) ^ h ≤ 2 ^ (h / 2 + h / 2 + 1) :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 2 * (2 ^ (h / 2) * 2 ^ (h / 2)) := by
            rw [pow_succ, pow_add]
            ring
    have hs1 : 2 ^ (h / 2) * Nat.sqrt (M / 2 ^ h) ≤ Nat.sqrt M := by
      rw [Nat.le_sqrt]
      calc (2 ^ (h / 2) * Nat.sqrt (M / 2 ^ h)) *
          (2 ^ (h / 2) * Nat.sqrt (M / 2 ^ h))
          = (2 ^ (h / 2) * 2 ^ (h / 2)) *
              (Nat.sqrt (M / 2 ^ h) * Nat.sqrt (M / 2 ^ h)) := by ring
        _ ≤ (2 ^ (h / 2) * 2 ^ (h / 2)) * (M / 2 ^ h) := by
            apply Nat.mul_le_mul_left
            simpa [pow_two] using Nat.sqrt_le' (M / 2 ^ h)
        _ ≤ 2 ^ h * (M / 2 ^ h) := by
            apply Nat.mul_le_mul_right
            rw [← pow_add]
            exact Nat.pow_le_pow_right (by norm_num) (by omega)
        _ ≤ M := Nat.mul_div_le M (2 ^ h)
    have hs2 : (2:ℕ) ^ (h / 2) ≤ Nat.sqrt M := by
      rw [Nat.le_sqrt]
      calc (2:ℕ) ^ (h / 2) * 2 ^ (h / 2) = 2 ^ (h / 2 + h / 2) := by
            rw [pow_add]
        _ ≤ 2 ^ D := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ ≤ M := h2D
    calc 2 ^ h * (((F * B) / 2 ^ (h / 2)) * (Nat.sqrt (M / 2 ^ h) + 1))
        ≤ (2 * (2 ^ (h / 2) * 2 ^ (h / 2))) *
            (((F * B) / 2 ^ (h / 2)) * (Nat.sqrt (M / 2 ^ h) + 1)) :=
          Nat.mul_le_mul_right _ h1
      _ = 2 * ((2 ^ (h / 2) * ((F * B) / 2 ^ (h / 2))) *
            (2 ^ (h / 2) * Nat.sqrt (M / 2 ^ h) + 2 ^ (h / 2))) := by ring
      _ ≤ 2 * ((F * B) * (Nat.sqrt M + Nat.sqrt M)) := by
          apply Nat.mul_le_mul_left
          apply Nat.mul_le_mul
          · rw [mul_comm]
            exact Nat.div_mul_le_self _ _
          · exact Nat.add_le_add hs1 hs2
      _ = 4 * ((F * B) * Nat.sqrt M) := by ring
      _ ≤ 4 * ((F * B) * (Nat.sqrt M + 1)) := by
          apply Nat.mul_le_mul_left
          exact Nat.mul_le_mul_left _ (by omega)
  calc boostLedger F B M D
      ≤ ∑ _h ∈ range (D + 1), 4 * ((F * B) * (Nat.sqrt M + 1)) :=
        Finset.sum_le_sum hterm
    _ = 4 * (D + 1) * ((F * B) * (Nat.sqrt M + 1)) := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
        ring

/-- Per-sample cost of the plain pruned scan: at depth `h` the sample
visits `min(2^h, k)` nodes and enumerates the `A/2^h` levels of each -
POSITIONS ARE NEVER READ, so the cost is independent of the boost. -/
def scanLedger (k A D : ℕ) : ℕ :=
  ∑ h ∈ range (D + 1), min (2 ^ h) k * (A / 2 ^ h)

theorem scan_ledger (k A D : ℕ) : scanLedger k A D ≤ (D + 1) * A := by
  have hterm : ∀ h ∈ range (D + 1), min (2 ^ h) k * (A / 2 ^ h) ≤ A := by
    intro h _
    calc min (2 ^ h) k * (A / 2 ^ h)
        ≤ 2 ^ h * (A / 2 ^ h) := Nat.mul_le_mul_right _ (min_le_left _ _)
      _ ≤ A := Nat.mul_div_le A (2 ^ h)
  calc scanLedger k A D ≤ ∑ _h ∈ range (D + 1), A := Finset.sum_le_sum hterm
    _ = (D + 1) * A := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- **The resolution-lever headline.** With the p-bound certified by
`resolution_p_bound` (so `ρ = Θ(1/polylog)` and `N = Õ(ε⁻²)` suffices),
the composed statement: correctness, construction at boost
`Õ(n^{1.5})`-scale, and total sampling `Õ(n·ε⁻²)`-scale - uniformly,
with no residual ε-term and no ℓ anywhere in the costs:

    `Õ( n^{1.5} + n·ε⁻² )`. -/
theorem fprasUniform
    (S : List ℕ) (t : ℕ) (f : List Bool → ℚ)
    (hind : ∀ x, f x * f x = f x) (hf01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (ρ ε : ℚ) (hρ : 0 < ρ) (hε : 0 < ε)
    (hp : ρ ≤ expect1 (maskFinset S.length) (samplerMass S t) f)
    (N n k A F B M D E : ℕ) (hN : 0 < N)
    (hNbig : 1 ≤ N * (ε ^ 2 * ρ ^ 2))
    (hA : A ≤ n) (hM : M ≤ 2 * n) (h2D : 2 ^ D ≤ M)
    (hFB : F * B ≤ 8 * n) (hNE : N ≤ E) :
    -- correctness at N samples (with ρ = 1/polylog via the p-bound)
    ((∑ v ∈ (vecs (maskFinset S.length) N).filter
        (fun v => ε * expect1 (maskFinset S.length) (samplerMass S t) f ≤
          |sumStat f v / N - expect1 (maskFinset S.length) (samplerMass S t) f|),
      prodMass (samplerMass S t) v) ≤ 1 / 4) ∧
    -- construction at boost: Õ(n^{1.5})-scale, ε- and ℓ-free
    boostLedger F B M D ≤ 32 * (D + 1) * (n * (Nat.sqrt (2 * n) + 1)) ∧
    -- per-sample scan is boost-independent; total sampling Õ(n·ε⁻²)
    scanLedger k A D ≤ (D + 1) * n ∧
    N * scanLedger k A D ≤ (D + 1) * (n * E) := by
  have hscan : scanLedger k A D ≤ (D + 1) * A := scan_ledger k A D
  refine ⟨fpras_relative S t f hind hf01 ρ ε hρ hε hp N hN hNbig, ?_, ?_, ?_⟩
  · calc boostLedger F B M D
        ≤ 4 * (D + 1) * ((F * B) * (Nat.sqrt M + 1)) :=
          boost_construction_ledger F B M D h2D
      _ ≤ 4 * (D + 1) * ((8 * n) * (Nat.sqrt (2 * n) + 1)) := by
          apply Nat.mul_le_mul_left
          exact Nat.mul_le_mul hFB
            (Nat.add_le_add_right (Nat.sqrt_le_sqrt hM) 1)
      _ = 32 * (D + 1) * (n * (Nat.sqrt (2 * n) + 1)) := by ring
  · exact le_trans hscan (Nat.mul_le_mul_left _ hA)
  · calc N * scanLedger k A D ≤ N * ((D + 1) * A) :=
          Nat.mul_le_mul_left _ hscan
      _ ≤ E * ((D + 1) * n) := Nat.mul_le_mul hNE (Nat.mul_le_mul_left _ hA)
      _ = (D + 1) * (n * E) := by ring
