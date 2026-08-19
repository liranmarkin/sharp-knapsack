/-
# The headline theorem: `fprasSharp`

The single machine-checked statement of the new result, mirroring
`fptasSharp` on the FPTAS side. It conjoins:

1. **Correctness** - `N` independent runs of the verified sampler estimate
   any indicator probability `p ≥ ρ` within relative error `ε`, except
   with probability at most `1/4` (Stages A-C composed);
2. **Cost** - `N` samples times the per-sample cost ledger stay within the
   `min(n√ℓ, n²/ℓ)·ε⁻²` budget, whose cube is at most
   `4194304·(D+1)·n⁴·E³` - i.e. the sampling work is
   `Õ(n^{4/3}·ε⁻²)`, strictly below Feng-Jin's `Õ(n^{1.5}·ε⁻²)` for
   every `ε = o(1)`.

The cost unit is one node-draw of the pruned descent
(`docs/witness-sampler.md`, cost ledger): `E` stands for `⌈ε⁻²⌉`, `A ≤ n`
for the subtree item count, `B ≤ 8ℓ` for the array-length scale, `k ≤ 8ℓ`
for the per-sample item count, `D` for the tree depth, and `N·ℓ ≤ n·E`
for the Lemma 3.3 sample budget (machine-checked as `lemma_33`). The one
assumption living outside Lean is the witness-oracle speed (Feng-Jin's
own Theorem 6.1 subroutine) realizing this unit.
-/
import SharpKnapsack.New.SamplerInstance
import SharpKnapsack.New.SamplerLedger

open Finset

/-- Per-sample cost in ledger units: at each depth, the pruned visit count
times the per-node draw cost (level enumeration capped by the scan). -/
def perSampleLedger (k A B D : ℕ) : ℕ :=
  ∑ h ∈ range (D + 1), min (2 ^ h) k * min (A / 2 ^ h) (B / 2 ^ (h / 2))

/-- The per-sample ledger is bounded by both cost modes at once. -/
theorem perSampleLedger_le (k A B D : ℕ) :
    perSampleLedger k A B D ≤
      min ((D + 1) * A) (32 * B * (Nat.sqrt k + 1)) := by
  apply le_min
  · calc perSampleLedger k A B D
        ≤ ∑ h ∈ range (D + 1), min (2 ^ h) k * (A / 2 ^ h) := by
          apply Finset.sum_le_sum
          intro h _
          exact Nat.mul_le_mul_left _ (min_le_left _ _)
      _ ≤ (D + 1) * A := ledger_flat A k (D + 1)
  · calc perSampleLedger k A B D
        ≤ ∑ h ∈ range (D + 1), min (2 ^ h) k * (B / 2 ^ (h / 2)) := by
          apply Finset.sum_le_sum
          intro h _
          exact Nat.mul_le_mul_left _ (min_le_right _ _)
      _ ≤ 32 * B * (Nat.sqrt k + 1) := ledger_sqrt B k (D + 1)

/-- **The headline theorem.** For any instance and any `[0,1]`-indicator
with true probability at least `ρ` under the uniform solution
distribution: `N` independent samples estimate it within relative error
`ε` except with probability `≤ 1/4`, and the total sampling work obeys
the `Õ(n^{4/3}·ε⁻²)` ledger - the machine-checked form of

    `Õ(n^{1.5} + min(n√ℓ, n²/ℓ)·ε⁻²)  ≤  Õ(n^{1.5} + n^{4/3}·ε⁻²)`. -/
theorem fprasSharp
    (S : List ℕ) (t : ℕ) (f : List Bool → ℚ)
    (hind : ∀ x, f x * f x = f x) (hf01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (ρ ε : ℚ) (hρ : 0 < ρ) (hε : 0 < ε)
    (hp : ρ ≤ expect1 (maskFinset S.length) (samplerMass S t) f)
    (N n ℓ k A B D E : ℕ) (hN : 0 < N)
    (hNbig : 1 ≤ N * (ε ^ 2 * ρ ^ 2))
    (hℓ : 0 < ℓ) (hA : A ≤ n) (hB : B ≤ 8 * ℓ) (hk : k ≤ 8 * ℓ)
    (hNE : N * ℓ ≤ n * E) :
    -- (1) correctness, composed from the verified sampler and estimator
    ((∑ v ∈ (vecs (maskFinset S.length) N).filter
        (fun v => ε * expect1 (maskFinset S.length) (samplerMass S t) f ≤
          |sumStat f v / N - expect1 (maskFinset S.length) (samplerMass S t) f|),
      prodMass (samplerMass S t) v) ≤ 1 / 4) ∧
    -- (2) cost: the two ledger modes ...
    (N * perSampleLedger k A B D) * ℓ ≤ (D + 1) * (n * n * E) ∧
    N * perSampleLedger k A B D ≤ 1024 * (Nat.sqrt ℓ + 1) * (n * E) ∧
    -- ... collapse to the n^{4/3} form
    (N * perSampleLedger k A B D) ^ 3 ≤ 4194304 * (D + 1) * (n ^ 4 * E ^ 3) := by
  refine ⟨fpras_relative S t f hind hf01 ρ ε hρ hε hp N hN hNbig, ?_, ?_, ?_⟩
  case _ =>
    -- mode 1: (N·per)·ℓ ≤ (D+1)·n²·E
    have h1 : perSampleLedger k A B D ≤ (D + 1) * A :=
      le_trans (perSampleLedger_le k A B D) (min_le_left _ _)
    calc (N * perSampleLedger k A B D) * ℓ
        ≤ (N * ((D + 1) * A)) * ℓ :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h1)
      _ = (D + 1) * (A * (N * ℓ)) := by ring
      _ ≤ (D + 1) * (n * (n * E)) := by
          apply Nat.mul_le_mul_left
          exact Nat.mul_le_mul hA hNE
      _ = (D + 1) * (n * n * E) := by ring
  case _ =>
    -- mode 2: N·per ≤ 1024·(√ℓ+1)·n·E
    have h2 : perSampleLedger k A B D ≤ 32 * B * (Nat.sqrt k + 1) :=
      le_trans (perSampleLedger_le k A B D) (min_le_right _ _)
    have hsk : Nat.sqrt k + 1 ≤ 4 * (Nat.sqrt ℓ + 1) := by
      have hk8 : Nat.sqrt k ≤ Nat.sqrt (8 * ℓ) := Nat.sqrt_le_sqrt hk
      have h8 : Nat.sqrt (8 * ℓ) ≤ 3 * (Nat.sqrt ℓ + 1) := by
        have hle : 8 * ℓ ≤ (3 * (Nat.sqrt ℓ + 1)) * (3 * (Nat.sqrt ℓ + 1)) := by
          have h11 := Nat.lt_succ_sqrt ℓ
          simp only [Nat.succ_eq_add_one] at h11
          nlinarith [Nat.sqrt_le' ℓ, Nat.zero_le (Nat.sqrt ℓ)]
        calc Nat.sqrt (8 * ℓ)
            ≤ Nat.sqrt ((3 * (Nat.sqrt ℓ + 1)) * (3 * (Nat.sqrt ℓ + 1))) :=
              Nat.sqrt_le_sqrt hle
          _ = 3 * (Nat.sqrt ℓ + 1) := Nat.sqrt_eq _
      omega
    calc N * perSampleLedger k A B D
        ≤ N * (32 * B * (Nat.sqrt k + 1)) := Nat.mul_le_mul_left _ h2
      _ ≤ N * (32 * (8 * ℓ) * (4 * (Nat.sqrt ℓ + 1))) := by
          apply Nat.mul_le_mul_left
          exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hB) hsk
      _ = 1024 * (Nat.sqrt ℓ + 1) * (N * ℓ) := by ring
      _ ≤ 1024 * (Nat.sqrt ℓ + 1) * (n * E) := Nat.mul_le_mul_left _ hNE
  case _ =>
    -- the collapse: cube ≤ mode1 · mode2², with (√ℓ+1)² ≤ 4ℓ cancelling ℓ
    have h1 : perSampleLedger k A B D ≤ (D + 1) * A :=
      le_trans (perSampleLedger_le k A B D) (min_le_left _ _)
    have h2 : perSampleLedger k A B D ≤ 32 * B * (Nat.sqrt k + 1) :=
      le_trans (perSampleLedger_le k A B D) (min_le_right _ _)
    -- reuse the two modes (re-derive to keep the cases independent)
    have hm1 : (N * perSampleLedger k A B D) * ℓ ≤ (D + 1) * (n * n * E) := by
      calc (N * perSampleLedger k A B D) * ℓ
          ≤ (N * ((D + 1) * A)) * ℓ :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h1)
        _ = (D + 1) * (A * (N * ℓ)) := by ring
        _ ≤ (D + 1) * (n * (n * E)) := by
            apply Nat.mul_le_mul_left
            exact Nat.mul_le_mul hA hNE
        _ = (D + 1) * (n * n * E) := by ring
    have hsk : Nat.sqrt k + 1 ≤ 4 * (Nat.sqrt ℓ + 1) := by
      have hk8 : Nat.sqrt k ≤ Nat.sqrt (8 * ℓ) := Nat.sqrt_le_sqrt hk
      have h8 : Nat.sqrt (8 * ℓ) ≤ 3 * (Nat.sqrt ℓ + 1) := by
        have hle : 8 * ℓ ≤ (3 * (Nat.sqrt ℓ + 1)) * (3 * (Nat.sqrt ℓ + 1)) := by
          have h11 := Nat.lt_succ_sqrt ℓ
          simp only [Nat.succ_eq_add_one] at h11
          nlinarith [Nat.sqrt_le' ℓ, Nat.zero_le (Nat.sqrt ℓ)]
        calc Nat.sqrt (8 * ℓ)
            ≤ Nat.sqrt ((3 * (Nat.sqrt ℓ + 1)) * (3 * (Nat.sqrt ℓ + 1))) :=
              Nat.sqrt_le_sqrt hle
          _ = 3 * (Nat.sqrt ℓ + 1) := Nat.sqrt_eq _
      omega
    have hm2 : N * perSampleLedger k A B D ≤ 1024 * (Nat.sqrt ℓ + 1) * (n * E) := by
      calc N * perSampleLedger k A B D
          ≤ N * (32 * B * (Nat.sqrt k + 1)) := Nat.mul_le_mul_left _ h2
        _ ≤ N * (32 * (8 * ℓ) * (4 * (Nat.sqrt ℓ + 1))) := by
            apply Nat.mul_le_mul_left
            exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hB) hsk
        _ = 1024 * (Nat.sqrt ℓ + 1) * (N * ℓ) := by ring
        _ ≤ 1024 * (Nat.sqrt ℓ + 1) * (n * E) := Nat.mul_le_mul_left _ hNE
    set c := N * perSampleLedger k A B D with hc
    have hsq : (Nat.sqrt ℓ + 1) * (Nat.sqrt ℓ + 1) ≤ 4 * ℓ := by
      have h12 := Nat.sqrt_le' ℓ
      have h13 : Nat.sqrt ℓ ≤ ℓ := Nat.sqrt_le_self ℓ
      nlinarith
    have hkey : c ^ 3 * ℓ ≤ (4194304 * (D + 1) * (n ^ 4 * E ^ 3)) * ℓ := by
      calc c ^ 3 * ℓ = (c * ℓ) * (c * c) := by ring
        _ ≤ ((D + 1) * (n * n * E)) * ((1024 * (Nat.sqrt ℓ + 1) * (n * E)) *
            (1024 * (Nat.sqrt ℓ + 1) * (n * E))) := by
            apply Nat.mul_le_mul hm1
            exact Nat.mul_le_mul hm2 hm2
        _ = (D + 1) * 1048576 * ((Nat.sqrt ℓ + 1) * (Nat.sqrt ℓ + 1)) *
            (n ^ 4 * E ^ 3) := by ring
        _ ≤ (D + 1) * 1048576 * (4 * ℓ) * (n ^ 4 * E ^ 3) := by
            apply Nat.mul_le_mul_right
            exact Nat.mul_le_mul_left _ hsq
        _ = (4194304 * (D + 1) * (n ^ 4 * E ^ 3)) * ℓ := by ring
    exact Nat.le_of_mul_le_mul_right hkey hℓ

/-! ### The amortized headline (branch `beyond-n43`) -/

/-- Cache-build cost over a class tree: at depth `h`, up to `2^h` nodes
each build alias tables for at most `B/2^(h/2)` distinct positions
(the array length bounds distinct queries), at `A/2^h` per build. -/
def cacheLedger (A B D : ℕ) : ℕ :=
  ∑ h ∈ range (D + 1), 2 ^ h * ((B / 2 ^ (h / 2)) * (A / 2 ^ h))

/-- **The amortized headline theorem.** Everything `fprasSharp` states,
plus the amortized-cache mode: cache builds are ε-FREE
(`cacheLedger ≤ 32·ℓ·n`) and post-cache draws are output-linear
(`N·k ≤ 8·n·E`). With `cache_collapse` and `ledger_collapse` certifying
the exponents, the total sampling work is

    `Õ( min(n^{4/3}·ε⁻², n^{1.5}·ε⁻¹) + n·ε⁻² )`

- dominating the `fprasSharp` bound for every `ε < n^{-1/6}` and tending
to the output-optimal `n·ε⁻²` as `ε → 0`. -/
theorem fprasSharper
    (S : List ℕ) (t : ℕ) (f : List Bool → ℚ)
    (hind : ∀ x, f x * f x = f x) (hf01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (ρ ε : ℚ) (hρ : 0 < ρ) (hε : 0 < ε)
    (hp : ρ ≤ expect1 (maskFinset S.length) (samplerMass S t) f)
    (N n ℓ k A B D E : ℕ) (hN : 0 < N)
    (hNbig : 1 ≤ N * (ε ^ 2 * ρ ^ 2))
    (hℓ : 0 < ℓ) (hA : A ≤ n) (hB : B ≤ 8 * ℓ) (hk : k ≤ 8 * ℓ)
    (hNE : N * ℓ ≤ n * E) :
    -- correctness and the two enumeration modes, as in `fprasSharp`
    ((∑ v ∈ (vecs (maskFinset S.length) N).filter
        (fun v => ε * expect1 (maskFinset S.length) (samplerMass S t) f ≤
          |sumStat f v / N - expect1 (maskFinset S.length) (samplerMass S t) f|),
      prodMass (samplerMass S t) v) ≤ 1 / 4) ∧
    (N * perSampleLedger k A B D) * ℓ ≤ (D + 1) * (n * n * E) ∧
    N * perSampleLedger k A B D ≤ 1024 * (Nat.sqrt ℓ + 1) * (n * E) ∧
    (N * perSampleLedger k A B D) ^ 3 ≤ 4194304 * (D + 1) * (n ^ 4 * E ^ 3) ∧
    -- NEW: the amortized-cache mode - ε-free builds, output-linear draws
    cacheLedger A B D ≤ 32 * (ℓ * n) ∧
    N * k ≤ 8 * (n * E) := by
  obtain ⟨h1, h2, h3, h4⟩ := fprasSharp S t f hind hf01 ρ ε hρ hε hp
    N n ℓ k A B D E hN hNbig hℓ hA hB hk hNE
  refine ⟨h1, h2, h3, h4, ?_, ?_⟩
  · calc cacheLedger A B D ≤ 4 * (B * A) := cache_ledger B A D
      _ ≤ 4 * ((8 * ℓ) * n) := by
          apply Nat.mul_le_mul_left
          exact Nat.mul_le_mul hB hA
      _ = 32 * (ℓ * n) := by ring
  · calc N * k ≤ N * (8 * ℓ) := Nat.mul_le_mul_left _ hk
      _ = 8 * (N * ℓ) := by ring
      _ ≤ 8 * (n * E) := Nat.mul_le_mul_left _ hNE
