/-
# Stage E of the witness-sampler verification: cost of the pruned descent

Stage A.2 proved the ∅-split pruned sampler draws from the identical
distribution. This file proves what pruning buys: a sample whose mask
selects `k` items activates at most `(⌈log₂ n⌉ + 1) · k` nodes of the
recursion tree - the `Õ(k)` visit count in the cost ledger of
`docs/witness-sampler.md`. Together with Stage 0's `lazy_amortization` and
`ledger_collapse`, this machine-checks the structural (tree-shape) half of
the sampling cost; the per-node array-work model is Stage E.2.
-/
import SharpKnapsack.SamplerExact

open Finset

/-- Depth of the divide-and-conquer recursion tree. -/
def treeDepth (S : List ℕ) : ℕ :=
  if S.length ≤ 1 then 0
  else 1 + max (treeDepth (S.take (S.length / 2))) (treeDepth (S.drop (S.length / 2)))
termination_by S.length
decreasing_by
  · simp only [List.length_take]
    omega
  · simp only [List.length_drop]
    omega

/-- Nodes the pruned sampler descends into: those whose sub-mask selects at
least one item. (A skipped child costs `O(1)` at its parent, which is
accounted to the parent's own visit.) -/
def activeNodes (S : List ℕ) (m : List Bool) : ℕ :=
  if m.count true = 0 then 0
  else if S.length ≤ 1 then 1
  else 1 + activeNodes (S.take (S.length / 2)) (m.take (S.length / 2))
        + activeNodes (S.drop (S.length / 2)) (m.drop (S.length / 2))
termination_by S.length
decreasing_by
  · simp only [List.length_take]
    omega
  · simp only [List.length_drop]
    omega

theorem count_take_drop (m : List Bool) (k : ℕ) :
    (m.take k).count true + (m.drop k).count true = m.count true := by
  conv_rhs => rw [← List.take_append_drop k m]
  rw [List.count_append]

/-- **The pruning payoff**: a sample selecting `k` items activates at most
`(depth + 1) · k` nodes. -/
theorem activeNodes_le (S : List ℕ) (m : List Bool) :
    activeNodes S m ≤ (treeDepth S + 1) * m.count true := by
  induction hn : S.length using Nat.strong_induction_on generalizing S m with
  | _ n IH =>
  subst hn
  rw [activeNodes]
  by_cases hcnt : m.count true = 0
  · rw [if_pos hcnt]
    exact Nat.zero_le _
  rw [if_neg hcnt]
  have hk1 : 1 ≤ m.count true := Nat.one_le_iff_ne_zero.mpr hcnt
  by_cases hlen : S.length ≤ 1
  · rw [if_pos hlen]
    calc 1 ≤ m.count true := hk1
      _ ≤ (treeDepth S + 1) * m.count true := Nat.le_mul_of_pos_left _ (by omega)
  · rw [if_neg hlen]
    set k := S.length / 2 with hk
    have hL := IH (S.take k).length (by simp [List.length_take]; omega)
      (S.take k) (m.take k) rfl
    have hR := IH (S.drop k).length (by simp [List.length_drop]; omega)
      (S.drop k) (m.drop k) rfl
    have hdS : treeDepth S = 1 + max (treeDepth (S.take k)) (treeDepth (S.drop k)) := by
      conv_lhs => rw [treeDepth]
      rw [if_neg hlen, ← hk]
    have hmaxL := le_max_left (treeDepth (S.take k)) (treeDepth (S.drop k))
    have hmaxR := le_max_right (treeDepth (S.take k)) (treeDepth (S.drop k))
    have hdL : treeDepth (S.take k) + 1 ≤ treeDepth S := by omega
    have hdR : treeDepth (S.drop k) + 1 ≤ treeDepth S := by omega
    have hsplit := count_take_drop m k
    have hL' : activeNodes (S.take k) (m.take k) ≤
        treeDepth S * (m.take k).count true := by
      calc activeNodes (S.take k) (m.take k)
          ≤ (treeDepth (S.take k) + 1) * (m.take k).count true := hL
        _ ≤ treeDepth S * (m.take k).count true :=
            Nat.mul_le_mul_right _ (by omega)
    have hR' : activeNodes (S.drop k) (m.drop k) ≤
        treeDepth S * (m.drop k).count true := by
      calc activeNodes (S.drop k) (m.drop k)
          ≤ (treeDepth (S.drop k) + 1) * (m.drop k).count true := hR
        _ ≤ treeDepth S * (m.drop k).count true :=
            Nat.mul_le_mul_right _ (by omega)
    calc 1 + activeNodes (S.take k) (m.take k) + activeNodes (S.drop k) (m.drop k)
        ≤ 1 + treeDepth S * (m.take k).count true
            + treeDepth S * (m.drop k).count true := by omega
      _ = 1 + treeDepth S * m.count true := by
          rw [← hsplit, Nat.mul_add]
          omega
      _ ≤ (treeDepth S + 1) * m.count true := by
          have h2 : (treeDepth S + 1) * m.count true =
              treeDepth S * m.count true + m.count true := by ring
          omega

/-- The tree depth is logarithmic: `treeDepth S ≤ ⌈log₂ |S|⌉`. -/
theorem treeDepth_le (S : List ℕ) : treeDepth S ≤ Nat.clog 2 (max S.length 1) := by
  induction hn : S.length using Nat.strong_induction_on generalizing S with
  | _ n IH =>
  subst hn
  rw [treeDepth]
  by_cases hlen : S.length ≤ 1
  · rw [if_pos hlen]
    exact Nat.zero_le _
  · rw [if_neg hlen]
    set k := S.length / 2 with hk
    have hL := IH (S.take k).length (by simp [List.length_take]; omega) (S.take k) rfl
    have hR := IH (S.drop k).length (by simp [List.length_drop]; omega) (S.drop k) rfl
    have hLlen : (S.take k).length = k := by
      simp [List.length_take]
      omega
    have hRlen : (S.drop k).length = S.length - k := by
      simp [List.length_drop]
    have hclog : Nat.clog 2 ((S.length + 1) / 2) + 1 = Nat.clog 2 S.length := by
      conv_rhs => rw [Nat.clog_of_two_le (by norm_num) (by omega : 2 ≤ S.length)]
      rw [show S.length + 2 - 1 = S.length + 1 from by omega]
    have hmax : max S.length 1 = S.length := by omega
    rw [hmax]
    have hLb : Nat.clog 2 (max (S.take k).length 1) ≤ Nat.clog 2 ((S.length + 1) / 2) := by
      apply Nat.clog_mono_right
      rw [hLlen]
      omega
    have hRb : Nat.clog 2 (max (S.drop k).length 1) ≤ Nat.clog 2 ((S.length + 1) / 2) := by
      apply Nat.clog_mono_right
      rw [hRlen]
      omega
    omega

/-- Assembled: per-sample active nodes are at most `(⌈log₂ n⌉ + 1) · k`. -/
theorem sampler_visit_bound (S : List ℕ) (m : List Bool) :
    activeNodes S m ≤ (Nat.clog 2 (max S.length 1) + 1) * m.count true := by
  calc activeNodes S m ≤ (treeDepth S + 1) * m.count true := activeNodes_le S m
    _ ≤ (Nat.clog 2 (max S.length 1) + 1) * m.count true :=
        Nat.mul_le_mul_right _ (by have := treeDepth_le S; omega)
