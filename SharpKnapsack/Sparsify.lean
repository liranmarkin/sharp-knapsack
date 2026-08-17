/-
# Sparsification (paper Algorithm 1 and Lemma 8)

`sparsify δ L` compresses a sparse function into one with few points while
changing its prefix sums by at most a factor `1 + δ`. This is the paper's
Algorithm 1: scan the points in order of position, accumulating the prefix sum
`acc`; maintain a threshold `r` that grows geometrically (`r ← max(r+1,
⌊(1+δ)r⌋)`); each time `acc` reaches `r`, the current position becomes a
*breakpoint*. The output has one point per breakpoint, carrying the total mass
of its segment (mass between breakpoints is moved *left*, onto the previous
breakpoint, which can only inflate a prefix sum - by less than one threshold
step, hence by at most `1+δ`).

The scan state is `(acc, r, pending)` where `pending = some (q, base)` records
the last breakpoint position `q` and the prefix sum `base` just before it;
the value of the output point at `q` is only known once the *next* breakpoint
is found (or the scan ends).

**Lemma 8** (`sparsify_spec`): `sparsify δ L` is a `(1+δ)`-sum approximation
of `L`, and is well-formed.
-/

import SharpKnapsack.Sparse

open Finset

/-! ## The threshold sequence -/

/-- One step of the threshold sequence: `r ← max (r+1) ⌊(1+δ)r⌋`. -/
def nextR (δ : ℚ) (r : ℕ) : ℕ := max (r + 1) ⌊(1 + δ) * r⌋₊

/-- Bump the threshold until it exceeds `target` (the accumulated sum that
just crossed the old threshold). -/
def bumpR (δ : ℚ) (r target : ℕ) : ℕ :=
  if r ≤ target then bumpR δ (nextR δ r) target else r
termination_by target + 1 - r
decreasing_by
  have h : r + 1 ≤ nextR δ r := Nat.le_max_left _ _
  omega

theorem bumpR_gt (δ : ℚ) (r target : ℕ) : target < bumpR δ r target := by
  induction r using bumpR.induct δ target with
  | case1 r hle ih => rw [bumpR, if_pos hle]; exact ih
  | case2 r hgt => rw [bumpR, if_neg hgt]; omega

/-- The final threshold does not overshoot: it is at most
`max (target+1) ((1+δ)·target)`, because its predecessor was `≤ target`.
This is what makes the paper's Lemma 8 case analysis work. -/
theorem bumpR_le (δ : ℚ) (hδ : 0 ≤ δ) (r target : ℕ) (h : r ≤ target) :
    (bumpR δ r target : ℚ) ≤ max ((target : ℚ) + 1) ((1 + δ) * target) := by
  induction r using bumpR.induct δ target with
  | case1 r hle ih =>
    rw [bumpR, if_pos hle]
    by_cases h2 : nextR δ r ≤ target
    · exact ih h2
    · rw [bumpR, if_neg h2]
      rcases max_cases (r + 1) ⌊(1 + δ) * r⌋₊ with ⟨heq, _⟩ | ⟨heq, _⟩ <;>
        rw [nextR, heq]
      · refine le_trans ?_ (le_max_left _ _)
        exact_mod_cast Nat.add_le_add_right hle 1
      · refine le_trans ?_ (le_max_right _ _)
        have h1 : ((⌊(1 + δ) * r⌋₊ : ℚ)) ≤ (1 + δ) * r :=
          Nat.floor_le (by positivity)
        refine le_trans h1 ?_
        have : (r : ℚ) ≤ target := by exact_mod_cast hle
        nlinarith
  | case2 r hgt => omega

/-! ## Helper facts about prefix sums of sparse lists -/

namespace SparseFun

/-- A prefix sum is at most the total mass. -/
theorem prefixLe_eval_le_total (P : SparseFun) (x : ℕ) :
    prefixLe (eval P) x ≤ (P.map (·.2)).sum := by
  induction P with
  | nil => simp [eval_nil, prefixLe]
  | cons p P ih =>
    obtain ⟨a, v⟩ := p
    have h : eval ((a, v) :: P) = fun t => single a v t + eval P t :=
      funext fun t => eval_cons a v P t
    rw [h, prefixLe_add, prefixLe_single]
    simp only [List.map_cons, List.sum_cons]
    have : (if a ≤ x then v else 0) ≤ v := by split <;> omega
    omega

/-- If every point lies strictly right of `x`, the prefix sum at `x` is `0`. -/
theorem prefixLe_eval_eq_zero {M : SparseFun} {x : ℕ} (h : ∀ p ∈ M, x < p.1) :
    prefixLe (eval M) x = 0 := by
  induction M with
  | nil => simp [eval_nil, prefixLe]
  | cons p M ih =>
    obtain ⟨a, v⟩ := p
    have he : eval ((a, v) :: M) = fun t => single a v t + eval M t :=
      funext fun t => eval_cons a v M t
    rw [he, prefixLe_add, prefixLe_single, ih (fun q hq => h q (by simp [hq]))]
    have ha : ¬ a ≤ x := by
      have := h (a, v) (by simp)
      simp at this
      omega
    simp [ha]

/-- If every point lies at position `≤ x`, the prefix sum at `x` is the total. -/
theorem prefixLe_eval_eq_total {P : SparseFun} {x : ℕ} (h : ∀ p ∈ P, p.1 ≤ x) :
    prefixLe (eval P) x = (P.map (·.2)).sum := by
  induction P with
  | nil => simp [eval_nil, prefixLe]
  | cons p P ih =>
    obtain ⟨a, v⟩ := p
    have he : eval ((a, v) :: P) = fun t => single a v t + eval P t :=
      funext fun t => eval_cons a v P t
    rw [he, prefixLe_add, prefixLe_single, ih (fun q hq => h q (by simp [hq]))]
    have ha : a ≤ x := by
      have := h (a, v) (by simp)
      simpa using this
    simp [ha]

/-! ## The scan -/

/-- The sparsification scan. Arguments: remaining points (sorted), accumulated
sum `acc` of all points already consumed, current threshold `r`, and the
pending breakpoint (position, prefix sum just before it), if any. -/
def sparsifyGo (δ : ℚ) : List (ℕ × ℕ) → ℕ → ℕ → Option (ℕ × ℕ) → SparseFun
  | [], _, _, none => []
  | [], acc, _, some (q, base) => [(q, acc - base)]
  | (p, v) :: rest, acc, r, pending =>
    if acc + v < r then
      sparsifyGo δ rest (acc + v) r pending
    else
      (match pending with
        | none => []
        | some (q, base) => [(q, acc - base)]) ++
      sparsifyGo δ rest (acc + v) (bumpR δ r (acc + v)) (some (p, acc))

/-- Algorithm 1: sparsify a (sorted) representation with parameter `δ`. -/
def sparsify (δ : ℚ) (L : SparseFun) : SparseFun := sparsifyGo δ L 0 1 none

theorem sparsifyGo_nil_some (δ : ℚ) (acc r q base : ℕ) :
    sparsifyGo δ [] acc r (some (q, base)) = [(q, acc - base)] := rfl

theorem sparsifyGo_cons_lt {δ : ℚ} {p v acc r : ℕ} {rest : List (ℕ × ℕ)}
    {pending : Option (ℕ × ℕ)} (h : acc + v < r) :
    sparsifyGo δ ((p, v) :: rest) acc r pending
      = sparsifyGo δ rest (acc + v) r pending := by
  rw [sparsifyGo.eq_def]
  simp [h]

theorem sparsifyGo_cons_ge_some {δ : ℚ} {p v acc r q base : ℕ}
    {rest : List (ℕ × ℕ)} (h : ¬ acc + v < r) :
    sparsifyGo δ ((p, v) :: rest) acc r (some (q, base))
      = (q, acc - base) :: sparsifyGo δ rest (acc + v) (bumpR δ r (acc + v)) (some (p, acc)) := by
  rw [sparsifyGo.eq_def]
  simp [h]

theorem sparsifyGo_cons_ge_none {δ : ℚ} {p v acc r : ℕ}
    {rest : List (ℕ × ℕ)} (h : ¬ acc + v < r) :
    sparsifyGo δ ((p, v) :: rest) acc r none
      = sparsifyGo δ rest (acc + v) (bumpR δ r (acc + v)) (some (p, acc)) := by
  rw [sparsifyGo.eq_def]
  simp [h]

/-! ## The main invariant

`sparsifyGo_spec` is the heart of Lemma 8. The state is described relative to
the *processed prefix* `P` (a ghost variable: it appears only in the
hypotheses). Writing `f = eval (P ++ rest)` for the full input function:

* `acc` is the total mass of `P`;
* the pending breakpoint `q` lies left of everything in `rest`, and `base`
  (the prefix sum just before `q`) is strictly below `acc`;
* the threshold `r` is above `acc` but at most `max (f^≤(q)+1) ((1+δ)·f^≤(q))`
  - it was set by `bumpR` when the breakpoint at `q` was created.

The conclusion: the output `R`, offset by `base`, has prefix sums that
sandwich `f^≤` between itself and `(1+δ)·f^≤` on `[q, ∞)`, and `R` is a
well-formed representation living on positions `≥ q`.
-/

theorem sparsifyGo_spec (δ : ℚ) (hδ : 0 ≤ δ)
    (rest : List (ℕ × ℕ)) (P : SparseFun) (acc r q base : ℕ)
    (hsorted : (P ++ rest).Pairwise (fun p₁ p₂ => p₁.1 < p₂.1))
    (hpos : ∀ p ∈ P ++ rest, 0 < p.2)
    (hacc : acc = (P.map (·.2)).sum)
    (hbase_lt : base < acc)
    (hr : acc < r)
    (hrbound : (r : ℚ) ≤ max ((prefixLe (eval (P ++ rest)) q : ℚ) + 1)
        ((1 + δ) * prefixLe (eval (P ++ rest)) q))
    (hqlt : ∀ p ∈ rest, q < p.1) :
    (∀ p ∈ sparsifyGo δ rest acc r (some (q, base)), q ≤ p.1) ∧
    WF (sparsifyGo δ rest acc r (some (q, base))) ∧
    (∀ x, q ≤ x →
      prefixLe (eval (P ++ rest)) x
        ≤ base + prefixLe (eval (sparsifyGo δ rest acc r (some (q, base)))) x) ∧
    (∀ x, q ≤ x →
      ((base + prefixLe (eval (sparsifyGo δ rest acc r (some (q, base)))) x : ℕ) : ℚ)
        ≤ (1 + δ) * prefixLe (eval (P ++ rest)) x) := by
  induction rest generalizing P acc r q base with
  | nil =>
    rw [sparsifyGo_nil_some]
    have htotal : ∀ x, q ≤ x → prefixLe (eval (P ++ [])) x ≤ acc := by
      intro x _
      rw [List.append_nil, hacc]
      exact prefixLe_eval_le_total P x
    have hout : ∀ x, q ≤ x →
        base + prefixLe (eval [(q, acc - base)]) x = acc := by
      intro x hx
      have he : eval [(q, acc - base)] = fun t => single q (acc - base) t + eval [] t :=
        funext fun t => eval_cons q (acc - base) [] t
      rw [he, prefixLe_add, prefixLe_single]
      simp [eval_nil, prefixLe, hx]
      omega
    refine ⟨by simp, ⟨by simp, by simp; omega⟩, ?_, ?_⟩
    · intro x hx
      rw [hout x hx]
      exact htotal x hx
    · intro x hx
      rw [hout x hx]
      -- acc < r ≤ max (f^≤(q)+1) ((1+δ)·f^≤(q)), and f^≤(q) ≤ f^≤(x).
      have hmono : prefixLe (eval (P ++ [])) q ≤ prefixLe (eval (P ++ [])) x :=
        prefixLe_mono _ hx
      rcases max_cases ((prefixLe (eval (P ++ [])) q : ℚ) + 1)
          ((1 + δ) * prefixLe (eval (P ++ [])) q) with ⟨hm, _⟩ | ⟨hm, _⟩ <;>
        rw [hm] at hrbound
      · have hle : acc ≤ prefixLe (eval (P ++ [])) q := by
          have : (acc : ℚ) < prefixLe (eval (P ++ [])) q + 1 := by
            calc (acc : ℚ) < r := by exact_mod_cast hr
              _ ≤ _ := hrbound
          exact_mod_cast (by exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this))
        calc (acc : ℚ) ≤ prefixLe (eval (P ++ [])) q := by exact_mod_cast hle
          _ ≤ prefixLe (eval (P ++ [])) x := by exact_mod_cast hmono
          _ ≤ (1 + δ) * prefixLe (eval (P ++ [])) x := by nlinarith [Nat.cast_nonneg (α := ℚ) (prefixLe (eval (P ++ [])) x)]
      · calc (acc : ℚ) ≤ r := by exact_mod_cast le_of_lt hr
          _ ≤ (1 + δ) * prefixLe (eval (P ++ [])) q := hrbound
          _ ≤ (1 + δ) * prefixLe (eval (P ++ [])) x := by
              have : (prefixLe (eval (P ++ [])) q : ℚ) ≤ prefixLe (eval (P ++ [])) x := by
                exact_mod_cast hmono
              nlinarith
  | cons pv rest' ih =>
    obtain ⟨p, v⟩ := pv
    have hv : 0 < v := hpos (p, v) (by simp)
    -- Facts about the sorted structure.
    have hsplit := List.pairwise_append.mp hsorted
    have hPrest : ∀ pp ∈ P, ∀ pr ∈ (p, v) :: rest', pp.1 < pr.1 := hsplit.2.2
    have hrest : ((p, v) :: rest').Pairwise (fun p₁ p₂ => p₁.1 < p₂.1) := hsplit.2.1
    have hp_rest' : ∀ pr ∈ rest', p < pr.1 := by
      intro pr hpr
      exact (List.pairwise_cons.mp hrest).1 pr hpr
    -- Re-associate the list for the induction hypothesis.
    have hassoc : P ++ (p, v) :: rest' = (P ++ [(p, v)]) ++ rest' := by simp
    by_cases hbr : acc + v < r
    · -- No breakpoint at this point: it merges into the pending segment.
      rw [sparsifyGo_cons_lt hbr]
      have hsorted' : ((P ++ [(p, v)]) ++ rest').Pairwise (fun p₁ p₂ => p₁.1 < p₂.1) := by
        rwa [hassoc] at hsorted
      have hpos' : ∀ p' ∈ (P ++ [(p, v)]) ++ rest', 0 < p'.2 := by
        intro p' hp'
        exact hpos p' (by rw [hassoc]; exact hp')
      have hacc' : acc + v = ((P ++ [(p, v)]).map (·.2)).sum := by
        simp [hacc]
      have hrbound' : (r : ℚ) ≤ max ((prefixLe (eval ((P ++ [(p, v)]) ++ rest')) q : ℚ) + 1)
          ((1 + δ) * prefixLe (eval ((P ++ [(p, v)]) ++ rest')) q) := by
        rwa [hassoc] at hrbound
      have hqlt' : ∀ p' ∈ rest', q < p'.1 := fun p' hp' => hqlt p' (by simp [hp'])
      obtain ⟨c1, c2, c3, c4⟩ := ih (P ++ [(p, v)]) (acc + v) r q base
        hsorted' hpos' hacc' (by omega) hbr hrbound' hqlt'
      rw [hassoc]
      exact ⟨c1, c2, c3, c4⟩
    · -- Breakpoint: emit the pending point, start a new pending breakpoint at `p`.
      rw [sparsifyGo_cons_ge_some hbr]
      have hqp : q < p := hqlt (p, v) (by simp)
      -- Prefix sums of the full function at `p`: everything in `P` plus `v`.
      have hfp : prefixLe (eval (P ++ (p, v) :: rest')) p = acc + v := by
        have h1 : ∀ p' ∈ P ++ [(p, v)], p'.1 ≤ p := by
          intro p' hp'
          rcases List.mem_append.mp hp' with h | h
          · exact le_of_lt (hPrest p' h (p, v) (by simp))
          · simp at h; subst h; simp
        have h2 : ∀ p' ∈ rest', p < p'.1 := hp_rest'
        calc prefixLe (eval (P ++ (p, v) :: rest')) p
            = prefixLe (eval ((P ++ [(p, v)]) ++ rest')) p := by rw [← hassoc]
          _ = prefixLe (eval (P ++ [(p, v)])) p + prefixLe (eval rest') p :=
              prefixLe_eval_append _ _ p
          _ = acc + v := by
              rw [prefixLe_eval_eq_total h1, prefixLe_eval_eq_zero h2]
              simp [hacc]
    -- Invariant for the recursive call.
      have hsorted' : ((P ++ [(p, v)]) ++ rest').Pairwise (fun p₁ p₂ => p₁.1 < p₂.1) := by
        rwa [hassoc] at hsorted
      have hpos' : ∀ p' ∈ (P ++ [(p, v)]) ++ rest', 0 < p'.2 := by
        intro p' hp'
        exact hpos p' (by rw [hassoc]; exact hp')
      have hacc' : acc + v = ((P ++ [(p, v)]).map (·.2)).sum := by simp [hacc]
      have hrbound' : ((bumpR δ r (acc + v) : ℕ) : ℚ)
          ≤ max ((prefixLe (eval ((P ++ [(p, v)]) ++ rest')) p : ℚ) + 1)
            ((1 + δ) * prefixLe (eval ((P ++ [(p, v)]) ++ rest')) p) := by
        have hb := bumpR_le δ hδ r (acc + v) (by omega)
        have : prefixLe (eval ((P ++ [(p, v)]) ++ rest')) p = acc + v := by
          rw [← hassoc]; exact hfp
        rw [this]
        exact_mod_cast hb
      obtain ⟨c1, c2, c3, c4⟩ := ih (P ++ [(p, v)]) (acc + v) (bumpR δ r (acc + v)) p acc
        hsorted' hpos' hacc' (by omega) (bumpR_gt δ r (acc + v)) hrbound' hp_rest'
      set R' := sparsifyGo δ rest' (acc + v) (bumpR δ r (acc + v)) (some (p, acc)) with hR'
      -- Assemble the four conclusions for `(q, acc - base) :: R'`.
      have hkeys : ∀ p' ∈ (q, acc - base) :: R', q ≤ p'.1 := by
        intro p' hp'
        rcases List.mem_cons.mp hp' with rfl | hp'
        · simp
        · exact le_trans (le_of_lt hqp) (c1 p' hp')
      have hwf : WF ((q, acc - base) :: R') := by
        refine ⟨List.pairwise_cons.mpr ⟨?_, c2.1⟩, ?_⟩
        · intro p' hp'
          exact lt_of_lt_of_le hqp (c1 p' hp')
        · intro p' hp'
          rcases List.mem_cons.mp hp' with rfl | hp'
          · simp; omega
          · exact c2.2 p' hp'
      -- The output prefix sum, offset by `base`, equals `acc + (R' part)` at `x ≥ q`.
      have hout : ∀ x, q ≤ x →
          base + prefixLe (eval ((q, acc - base) :: R')) x
            = acc + prefixLe (eval R') x := by
        intro x hx
        have he : eval ((q, acc - base) :: R') = fun t => single q (acc - base) t + eval R' t :=
          funext fun t => eval_cons q (acc - base) R' t
        rw [he, prefixLe_add, prefixLe_single, if_pos hx]
        omega
      refine ⟨hkeys, hwf, ?_, ?_⟩
      · -- Lower bound.
        intro x hx
        rw [hout x hx]
        by_cases hxp : p ≤ x
        · have := c3 x hxp
          rw [← hassoc] at this
          exact this
        · -- q ≤ x < p: the prefix sum of the input at `x` is at most `acc`.
          have hfx : prefixLe (eval (P ++ (p, v) :: rest')) x ≤ acc := by
            have h2 : ∀ p' ∈ (p, v) :: rest', x < p'.1 := by
              intro p' hp'
              rcases List.mem_cons.mp hp' with rfl | hp'
              · exact (show x < p by omega)
              · have := hp_rest' p' hp'
                omega
            have h3 := prefixLe_eval_le_total P x
            rw [prefixLe_eval_append, prefixLe_eval_eq_zero h2, hacc]
            omega
          omega
      · -- Upper bound.
        intro x hx
        rw [hout x hx]
        by_cases hxp : p ≤ x
        · have := c4 x hxp
          rw [← hassoc] at this
          exact this
        · -- q ≤ x < p: output is `acc`; input prefix sum is at least `f^≤(q)`,
          -- and `acc < r ≤ max (f^≤(q)+1) ((1+δ)·f^≤(q))` - the paper's two cases.
          have hR'x : prefixLe (eval R') x = 0 := by
            refine prefixLe_eval_eq_zero ?_
            intro p' hp'
            have := c1 p' hp'
            omega
          rw [hR'x]
          have hmono : prefixLe (eval (P ++ (p, v) :: rest')) q
              ≤ prefixLe (eval (P ++ (p, v) :: rest')) x :=
            prefixLe_mono _ hx
          rcases max_cases ((prefixLe (eval (P ++ (p, v) :: rest')) q : ℚ) + 1)
              ((1 + δ) * prefixLe (eval (P ++ (p, v) :: rest')) q) with ⟨hm, _⟩ | ⟨hm, _⟩ <;>
            rw [hm] at hrbound
          · have hle : acc ≤ prefixLe (eval (P ++ (p, v) :: rest')) q := by
              have h1 : (acc : ℚ) < prefixLe (eval (P ++ (p, v) :: rest')) q + 1 := by
                calc (acc : ℚ) < r := by exact_mod_cast hr
                  _ ≤ _ := hrbound
              have h2 : acc < prefixLe (eval (P ++ (p, v) :: rest')) q + 1 := by
                exact_mod_cast h1
              omega
            have hlex : acc ≤ prefixLe (eval (P ++ (p, v) :: rest')) x := le_trans hle hmono
            calc ((acc + 0 : ℕ) : ℚ) = (acc : ℚ) := by norm_num
              _ ≤ prefixLe (eval (P ++ (p, v) :: rest')) x := by exact_mod_cast hlex
              _ ≤ (1 + δ) * prefixLe (eval (P ++ (p, v) :: rest')) x := by
                  nlinarith [Nat.cast_nonneg (α := ℚ) (prefixLe (eval (P ++ (p, v) :: rest')) x)]
          · calc ((acc + 0 : ℕ) : ℚ) = (acc : ℚ) := by norm_num
              _ ≤ r := by exact_mod_cast le_of_lt hr
              _ ≤ (1 + δ) * prefixLe (eval (P ++ (p, v) :: rest')) q := hrbound
              _ ≤ (1 + δ) * prefixLe (eval (P ++ (p, v) :: rest')) x := by
                  have : (prefixLe (eval (P ++ (p, v) :: rest')) q : ℚ)
                      ≤ prefixLe (eval (P ++ (p, v) :: rest')) x := by exact_mod_cast hmono
                  nlinarith

/-- **Lemma 8**: `sparsify δ L` is a `(1+δ)`-sum approximation of `L`,
and its representation is well-formed. -/
theorem sparsify_spec (δ : ℚ) (hδ : 0 ≤ δ) {L : SparseFun} (hWF : WF L) :
    IsSumApprox (1 + δ) (eval (sparsify δ L)) (eval L) ∧ WF (sparsify δ L) := by
  obtain ⟨hsorted, hpos⟩ := hWF
  unfold sparsify
  match L with
  | [] =>
    constructor
    · constructor <;> intro x <;> simp [sparsifyGo, eval_nil, prefixLe]
    · exact ⟨by simp [sparsifyGo], by simp [sparsifyGo]⟩
  | (p, v) :: rest =>
    have hv : 0 < v := hpos (p, v) (by simp)
    have hbr : ¬ 0 + v < 1 := by omega
    rw [sparsifyGo_cons_ge_none hbr]
    simp only [Nat.zero_add]
    have hp_rest : ∀ pr ∈ rest, p < pr.1 :=
      fun pr hpr => (List.pairwise_cons.mp hsorted).1 pr hpr
    -- Instantiate the invariant with `P = [(p, v)]`.
    have hfp : prefixLe (eval ([(p, v)] ++ rest)) p = v := by
      have h1 : ∀ p' ∈ ([(p, v)] : SparseFun), p'.1 ≤ p := by simp
      have h2 : ∀ p' ∈ rest, p < p'.1 := hp_rest
      rw [prefixLe_eval_append, prefixLe_eval_eq_total h1, prefixLe_eval_eq_zero h2]
      simp
    have hrbound : ((bumpR δ 1 v : ℕ) : ℚ)
        ≤ max ((prefixLe (eval ([(p, v)] ++ rest)) p : ℚ) + 1)
          ((1 + δ) * prefixLe (eval ([(p, v)] ++ rest)) p) := by
      have hb := bumpR_le δ hδ 1 v (by omega)
      rw [hfp]
      exact_mod_cast hb
    obtain ⟨c1, c2, c3, c4⟩ := sparsifyGo_spec δ hδ rest [(p, v)] v
      (bumpR δ 1 v) p 0
      (by simpa using hsorted) (by simpa using hpos) (by simp)
      hv (bumpR_gt δ 1 v) hrbound hp_rest
    refine ⟨⟨?_, ?_⟩, c2⟩
    · intro x
      by_cases hx : p ≤ x
      · have := c3 x hx
        simpa using this
      · -- x < p: both sides are 0.
        have hfx : prefixLe (eval ((p, v) :: rest)) x = 0 := by
          refine prefixLe_eval_eq_zero ?_
          intro p' hp'
          rcases List.mem_cons.mp hp' with rfl | hp'
          · exact (show x < p by omega)
          · have := hp_rest p' hp'
            omega
        rw [hfx]
        omega
    · intro x
      by_cases hx : p ≤ x
      · have := c4 x hx
        simpa using this
      · have hfx : prefixLe (eval ((p, v) :: rest)) x = 0 := by
          refine prefixLe_eval_eq_zero ?_
          intro p' hp'
          rcases List.mem_cons.mp hp' with rfl | hp'
          · exact (show x < p by omega)
          · have := hp_rest p' hp'
            omega
        have hRx : prefixLe (eval (sparsifyGo δ rest v (bumpR δ 1 v)
            (some (p, 0)))) x = 0 := by
          refine prefixLe_eval_eq_zero ?_
          intro p' hp'
          have := c1 p' hp'
          omega
        rw [hfx, hRx]
        simp

end SparseFun
