/-
# Barriers for deterministic #Knapsack merges (branch `det-fptas`)

Machine-checked core of barrier B1 from
`docs/research/2026-08-20-det-fptas-notes.md`:

**Ramp hardness.** The GMW sum-approximation merge, viewed on breakpoint
sequences, asks for a min-plus convolution of monotone sequences with
UNBOUNDED values. This is as hard as general min-plus convolution:
adding the linear ramp `R·k` to both inputs (i) shifts every
anti-diagonal of the min-plus convolution by exactly `R·m` - so the
ramped instance determines the original - and (ii) makes any
`B`-bounded sequence monotone once `R ≥ 2B`. Hence the fast
bounded-monotone MinConv algorithms (values in `[n]`; e.g.
Jin-Park-Saha-Xu 2026, deterministic n^{1.5+o(1)}) cannot apply to
breakpoint merges as-is: the unbounded-value monotone case they would
need is general-MinConv-hard.
-/
import Mathlib

open Finset

/-- Min-plus convolution at anti-diagonal `m`, with the split point
ranging over `0..n` (stated for the upper half `n ≤ m`, wlog by
symmetry of the two operands). -/
def minConvAt (a b : ℕ → ℤ) (n m : ℕ) : ℤ :=
  (range (n + 1)).inf' ⟨0, mem_range.mpr (Nat.succ_pos n)⟩ (fun k => a k + b (m - k))

/-- Adding a constant commutes with `inf'`. -/
theorem inf'_add_const (s : Finset ℕ) (hs : s.Nonempty) (f : ℕ → ℤ) (c : ℤ) :
    s.inf' hs (fun k => f k + c) = s.inf' hs f + c := by
  apply le_antisymm
  · obtain ⟨k, hk, hfk⟩ := Finset.exists_mem_eq_inf' hs f
    calc s.inf' hs (fun k => f k + c) ≤ f k + c := Finset.inf'_le _ hk
      _ = s.inf' hs f + c := by rw [← hfk]
  · apply Finset.le_inf'
    intro k hk
    have h1 : s.inf' hs f ≤ f k := Finset.inf'_le _ hk
    omega

/-- **B1, part (i): the ramp shifts every anti-diagonal uniformly.**
The min-plus convolution of the ramped sequences at anti-diagonal `m`
equals the original convolution plus `R·m` - so solving the ramped
(monotone) instance solves the general one. -/
theorem ramp_minConv (a b : ℕ → ℤ) (R : ℤ) (n m : ℕ) (hm : n ≤ m) :
    minConvAt (fun k => a k + R * k) (fun l => b l + R * l) n m =
      minConvAt a b n m + R * m := by
  have hne : (range (n + 1)).Nonempty := ⟨0, mem_range.mpr (Nat.succ_pos n)⟩
  have h1 : minConvAt (fun k => a k + R * k) (fun l => b l + R * l) n m =
      (range (n + 1)).inf' hne (fun k => (a k + b (m - k)) + R * m) := by
    apply Finset.inf'_congr _ rfl
    intro k hk
    have hkn : k ≤ n := by
      have := mem_range.mp hk
      omega
    have hkm : k ≤ m := le_trans hkn hm
    have hcast : ((m - k : ℕ) : ℤ) = (m : ℤ) - (k : ℤ) := by
      push_cast [Nat.cast_sub hkm]
      ring
    calc (a k + R * k) + (b (m - k) + R * ((m - k : ℕ) : ℤ))
        = (a k + b (m - k)) + R * ((k : ℤ) + ((m - k : ℕ) : ℤ)) := by ring
      _ = (a k + b (m - k)) + R * m := by
          rw [hcast]
          ring
  rw [h1, inf'_add_const]
  rfl

/-- **B1, part (ii): the ramp makes any bounded sequence monotone.**
If `|a k| ≤ B` on `0..n` and `R ≥ 2B`, then `k ↦ a k + R·k` is
monotone non-decreasing on `0..n`. So bounded-VALUE structure is
destroyed at exactly the moment monotonicity is gained: monotone
MinConv with unbounded values contains all of MinConv. -/
theorem ramp_monotone (a : ℕ → ℤ) (B R : ℤ) (n : ℕ)
    (hB : ∀ k ≤ n, -B ≤ a k ∧ a k ≤ B) (hR : 2 * B ≤ R) :
    ∀ k, k + 1 ≤ n → a k + R * k ≤ a (k + 1) + R * (k + 1) := by
  intro k hk
  have h1 := hB k (by omega)
  have h2 := hB (k + 1) hk
  have hcast : (((k + 1 : ℕ)) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
  have hgoal : a k - a (k + 1) ≤ R := by omega
  calc a k + R * k = a (k + 1) + (a k - a (k + 1)) + R * k := by ring
    _ ≤ a (k + 1) + R + R * k := by omega
    _ = a (k + 1) + R * ((k : ℤ) + 1) := by ring
    _ = a (k + 1) + R * ((k + 1 : ℕ) : ℤ) := by rw [hcast]

/-! ### The Pareto bound: exact-dominance crossings are linear

A pair `(k, l)` is *dominant* if no pair with a strictly larger index
sum has a position sum at most as small. Dominant pairs form a Pareto
staircase in (position-sum, index-sum): on every index-sum diagonal,
only a minimum-position cell can be dominant, so there are at most
`2s+1` of them. This is the `w = 0` pole of the in-band crossing
question: the s² blow-up of barrier B3 comes ENTIRELY from the
accuracy band, not from the dominance structure itself. -/

/-- Dominance: `p` is the lexicographic (position, index)-minimum on
its own diagonal, and every strictly higher diagonal sits at a strictly
larger position. These are exactly the `w = 0` in-band pairs. -/
def dominantPairs (x y : ℕ → ℤ) (s : ℕ) : Finset (ℕ × ℕ) :=
  ((range (s + 1)) ×ˢ (range (s + 1))).filter (fun p =>
    ∀ q ∈ (range (s + 1)) ×ˢ (range (s + 1)),
      (q.1 + q.2 = p.1 + p.2 →
        (x p.1 + y p.2 < x q.1 + y q.2 ∨
          (x p.1 + y p.2 = x q.1 + y q.2 ∧ p.1 ≤ q.1))) ∧
      (p.1 + p.2 < q.1 + q.2 → x p.1 + y p.2 < x q.1 + y q.2))

/-- **The Pareto bound.** At most one dominant pair per diagonal: the
map `(k, l) ↦ k + l` is injective on `dominantPairs`, so their number
is at most `2s + 1`. The s² blow-up of barrier B3 therefore comes
entirely from the accuracy band, not from the dominance structure. -/
theorem dominantPairs_card_le (x y : ℕ → ℤ) (s : ℕ) :
    (dominantPairs x y s).card ≤ 2 * s + 1 := by
  have hinj : ∀ p ∈ dominantPairs x y s, ∀ q ∈ dominantPairs x y s,
      p.1 + p.2 = q.1 + q.2 → p = q := by
    intro p hp q hq hsum
    rw [dominantPairs, mem_filter] at hp hq
    obtain ⟨hpmem, hpdom⟩ := hp
    obtain ⟨hqmem, hqdom⟩ := hq
    have h1 := (hpdom q hqmem).1 hsum.symm
    have h2 := (hqdom p hpmem).1 hsum
    have hfst : p.1 = q.1 := by
      rcases h1 with h1a | ⟨h1e, h1i⟩ <;> rcases h2 with h2a | ⟨h2e, h2i⟩ <;> omega
    have hsnd : p.2 = q.2 := by omega
    exact Prod.ext hfst hsnd
  calc (dominantPairs x y s).card
      = ((dominantPairs x y s).image (fun p => p.1 + p.2)).card := by
        rw [Finset.card_image_of_injOn]
        intro p hp q hq
        exact fun h => hinj p hp q hq h
    _ ≤ (range (2 * s + 1)).card := by
        apply Finset.card_le_card
        intro d hd
        obtain ⟨p, hp, hpd⟩ := Finset.mem_image.mp hd
        rw [dominantPairs, mem_filter, Finset.mem_product] at hp
        have h1 := mem_range.mp hp.1.1
        have h2 := mem_range.mp hp.1.2
        rw [mem_range]
        omega
    _ = 2 * s + 1 := Finset.card_range _

/-! ### B4: the GMW merge is conditionally optimal

Encode a (ramped, hence monotone - `ramp_monotone`) MinConv instance as
two breakpoint frontiers with unit value-steps: frontier `F` has its
`k`-th breakpoint at position `a k`, frontier `G` at `b l`. The merged
frontier's value at any position `t` is the max index-sum reachable
within position budget `t`; its inverse at index-sum `m` is exactly
`minConvAt a b n m` (`frontier_readoff` below). So any algorithm that
computes value-sparsified, position-exact merged frontiers - as every
GMW merge does - solves MinConv via `ramp_minConv`, and by the MinConv
hypothesis (and the Pareto-sum lower bound of Funke-Hespe-Sanders-
Storandt-Truschel, ESA 2023) cannot run in `s^{2-c}` worst-case. -/

/-- The merged frontier's value at position budget `t`: the largest
index-sum whose min-plus value fits within `t` (0 if none). -/
def frontierValue (a b : ℕ → ℤ) (n t : ℕ) : ℕ :=
  ((range (2 * n + 1)).filter (fun m => n ≤ m ∧ minConvAt a b n m ≤ t)).sup id

/-- **The read-off identity.** The merged frontier determines every
MinConv value: `minConvAt a b n m ≤ t` iff the frontier value at `t`
is at least `m` (on the monotone upper half, for nonneg inputs). Thus
inverting the frontier recovers the full MinConv - the encoding core of
the conditional-optimality barrier B4. -/
theorem frontier_readoff (a b : ℕ → ℤ) (n m t : ℕ)
    (hn : 1 ≤ n) (hm : n ≤ m) (hm2 : m ≤ 2 * n)
    (hmono : ∀ m₁ m₂, n ≤ m₁ → m₁ ≤ m₂ → m₂ ≤ 2 * n →
      minConvAt a b n m₁ ≤ minConvAt a b n m₂) :
    minConvAt a b n m ≤ t ↔ m ≤ frontierValue a b n t := by
  constructor
  · intro h
    apply Finset.le_sup (f := id)
    rw [mem_filter, mem_range]
    exact ⟨by omega, hm, h⟩
  · intro h
    by_cases hne : ((range (2 * n + 1)).filter
        (fun m' => n ≤ m' ∧ minConvAt a b n m' ≤ t)).Nonempty
    · obtain ⟨m', hm', hmax⟩ := Finset.exists_mem_eq_sup _ hne id
      have hval : frontierValue a b n t = m' := hmax
      rw [hval] at h
      rw [mem_filter, mem_range] at hm'
      calc minConvAt a b n m ≤ minConvAt a b n m' := by
            rcases Nat.le_total m m' with hle | hge
            · exact hmono m m' hm hle (by omega)
            · have : m = m' := by omega
              rw [this]
        _ ≤ t := hm'.2.2
    · exfalso
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [frontierValue, hne] at h
      simp at h
      omega

/-- Min-plus convolution of a monotone second operand is monotone in
the anti-diagonal index. -/
theorem minConvAt_mono (a b : ℕ → ℤ) (n : ℕ)
    (hb : ∀ i j, i ≤ j → b i ≤ b j) (m₁ m₂ : ℕ) (h : m₁ ≤ m₂) :
    minConvAt a b n m₁ ≤ minConvAt a b n m₂ := by
  apply Finset.le_inf'
  intro k hk
  calc minConvAt a b n m₁ ≤ a k + b (m₁ - k) := Finset.inf'_le _ hk
    _ ≤ a k + b (m₂ - k) := by
        have := hb (m₁ - k) (m₂ - k) (by omega)
        omega

/-- **B4, composed.** For ANY bounded integer sequences `a, b`, the
ramped encodings are monotone, and the value-sparsified position-exact
merged frontier of the encoded instances determines every MinConv
value of the ORIGINAL instance:
`minConvAt a b n m ≤ t − R·m  ↔  m ≤ frontierValue(ramped) t`.
Hence any subquadratic worst-case algorithm for the GMW merge step
would give subquadratic general MinConv - the merge is conditionally
optimal under the MinConv hypothesis. -/
theorem b4_merge_conditional_optimality
    (a b : ℕ → ℤ) (B : ℤ) (n m : ℕ) (t : ℤ)
    (hn : 1 ≤ n) (hm : n ≤ m) (hm2 : m ≤ 2 * n)
    (hB' : ∀ k ≤ 2 * n, -B ≤ b k ∧ b k ≤ B) :
    ∀ tn : ℕ, (t = (tn : ℤ)) →
      (minConvAt a b n m + (2 * B) * m ≤ t ↔
        m ≤ frontierValue (fun k => a k + (2 * B) * k)
          (fun l => b l + (2 * B) * l) n tn) := by
  intro tn ht
  have hmono : ∀ m₁ m₂, n ≤ m₁ → m₁ ≤ m₂ → m₂ ≤ 2 * n →
      minConvAt (fun k => a k + (2 * B) * k)
        (fun l => b l + (2 * B) * l) n m₁ ≤
      minConvAt (fun k => a k + (2 * B) * k)
        (fun l => b l + (2 * B) * l) n m₂ := by
    intro m₁ m₂ hm₁ h12 hm₂2
    apply Finset.le_inf'
    intro k hk
    have hkn : k ≤ n := by
      have := mem_range.mp hk
      omega
    calc minConvAt (fun k => a k + (2 * B) * k)
          (fun l => b l + (2 * B) * l) n m₁
        ≤ (a k + (2 * B) * k) + (b (m₁ - k) + (2 * B) * ((m₁ - k : ℕ) : ℤ)) :=
          Finset.inf'_le _ hk
      _ ≤ (a k + (2 * B) * k) + (b (m₂ - k) + (2 * B) * ((m₂ - k : ℕ) : ℤ)) := by
          have hstep : ∀ j, j + 1 ≤ 2 * n →
              b j + (2 * B) * j ≤ b (j + 1) + (2 * B) * (j + 1) := by
            intro j hj
            have := ramp_monotone b B (2 * B) (2 * n) hB' (le_refl _) j hj
            exact this
          have hmb : ∀ i j, i ≤ j → j ≤ 2 * n →
              b i + (2 * B) * i ≤ b j + (2 * B) * j := by
            intro i j hij hj2
            induction j with
            | zero =>
                have : i = 0 := by omega
                rw [this]
            | succ jj ih =>
                rcases Nat.lt_or_ge i (jj + 1) with hlt | hge
                · have h1 := ih (by omega) (by omega)
                  have h2 := hstep jj (by omega)
                  have hc1 : ((jj : ℤ) + 1) = ((jj + 1 : ℕ) : ℤ) := by push_cast; ring
                  calc b i + (2 * B) * i ≤ b jj + (2 * B) * jj := h1
                    _ ≤ b (jj + 1) + (2 * B) * ((jj : ℤ) + 1) := h2
                    _ = b (jj + 1) + (2 * B) * ((jj + 1 : ℕ) : ℤ) := by rw [hc1]
                · have : i = jj + 1 := by omega
                  rw [this]
          have := hmb (m₁ - k) (m₂ - k) (by omega) (by omega)
          omega
  have hR := ramp_minConv a b (2 * B) n m hm
  rw [ht]
  constructor
  · intro h
    rw [← frontier_readoff _ _ n m tn hn hm hm2 hmono]
    rw [hR]
    exact h
  · intro h
    rw [← hR]
    exact (frontier_readoff _ _ n m tn hn hm hm2 hmono).mpr h
