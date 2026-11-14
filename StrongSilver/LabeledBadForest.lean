-- SPDX-License-Identifier: GPL-3.0-only
import Mathlib.Data.Tree.Basic
import Mathlib.Tactic

namespace StrongSilver.BinaryForest
noncomputable section
variable {α : Type*}
set_option maxHeartbeats 2800000

/-- Number of bad internal vertices, retaining repeated occurrences. -/
def badNodeCount (good : BinaryTree α → Bool) : BinaryTree α → ℕ
  | .nil => 0
  | .node b l r => badNodeCount good l+badNodeCount good r+
      (if good (.node b l r) then 0 else 1)

/-- Height of the good component containing the root. A bad root cuts
both child components; a leaf is not a splitting vertex. -/
def goodComponentHeight (good : BinaryTree α → Bool) : BinaryTree α → ℕ
  | .nil => 0
  | .node b l r => if good (.node b l r) then
      1+max (goodComponentHeight good l) (goodComponentHeight good r) else 0

def AllGoodComponentsBounded (good : BinaryTree α → Bool) (m : ℕ) : BinaryTree α → Prop
  | .nil => True
  | .node b l r => goodComponentHeight good (.node b l r) ≤ m ∧
      AllGoodComponentsBounded good m l ∧ AllGoodComponentsBounded good m r

theorem goodComponentHeight_le {good : BinaryTree α → Bool} {m : ℕ} {t : BinaryTree α}
    (h : AllGoodComponentsBounded good m t) : goodComponentHeight good t ≤ m := by
  cases t with
  | nil => exact Nat.zero_le _
  | node b l r => exact h.1

/-- Deleting bad vertices leaves binary components of bounded height.
This estimate uses only the resulting component heights, with no
assumption about how many bad vertices occur on a path. -/
theorem nodeCount_bound_by_bad_components {good : BinaryTree α → Bool} {m : ℕ} {t : BinaryTree α}
    (h : AllGoodComponentsBounded good m t) :
    t.numNodes+1 ≤ 2^(m+1)*badNodeCount good t+2^(goodComponentHeight good t) := by
  induction t with
  | nil => simp [BinaryTree.numNodes,badNodeCount,goodComponentHeight]
  | node b l r il ir =>
    have hl := il h.2.1
    have hr := ir h.2.2
    have hls := goodComponentHeight_le h.2.1
    have hrs := goodComponentHeight_le h.2.2
    by_cases hg : good (.node b l r) = true
    · have hmaxL : 2^(goodComponentHeight good l) ≤ 2^(max (goodComponentHeight good l) (goodComponentHeight good r)) :=
        Nat.pow_le_pow_right (by decide) (le_max_left _ _)
      have hmaxR : 2^(goodComponentHeight good r) ≤ 2^(max (goodComponentHeight good l) (goodComponentHeight good r)) :=
        Nat.pow_le_pow_right (by decide) (le_max_right _ _)
      simp only [BinaryTree.numNodes,badNodeCount,goodComponentHeight,hg,↓reduceIte,add_zero]
      have hp : 2^(1+max (goodComponentHeight good l) (goodComponentHeight good r)) =
          2*2^(max (goodComponentHeight good l) (goodComponentHeight good r)) := by
        rw [Nat.pow_add]
      nlinarith only [hl,hr,hmaxL,hmaxR,hp]
    · have hgf := Bool.eq_false_iff.mpr hg
      have hmaxL : 2^(goodComponentHeight good l) ≤ 2^m := Nat.pow_le_pow_right (by decide) hls
      have hmaxR : 2^(goodComponentHeight good r) ≤ 2^m := Nat.pow_le_pow_right (by decide) hrs
      simp only [BinaryTree.numNodes,badNodeCount,goodComponentHeight,hgf,Bool.false_eq_true,↓reduceIte,pow_zero]
      have hp : 2^(goodComponentHeight good l)+2^(goodComponentHeight good r) ≤ 2^(m+1) := by
        rw [Nat.pow_succ]
        omega
      nlinarith only [hl,hr,hp]

theorem nodeCount_bound_by_bad_count {good : BinaryTree α → Bool} {m : ℕ} {t : BinaryTree α}
    (h : AllGoodComponentsBounded good m t) :
    t.numNodes ≤ 2^(m+1)*(badNodeCount good t+1) := by
  have hh := nodeCount_bound_by_bad_components h
  have he : 2^(goodComponentHeight good t) ≤ 2^(m+1) :=
    Nat.pow_le_pow_right (by decide) ((goodComponentHeight_le h).trans (Nat.le_succ m))
  nlinarith only [hh,he]

end
end StrongSilver.BinaryForest
