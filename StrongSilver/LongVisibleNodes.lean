-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.VisibleGapBudget
import StrongSilver.VisibilityWindowIntegral

namespace StrongSilver
open ScheduleTree ParentedScheduleNode Real Set
noncomputable section
set_option maxHeartbeats 4000000

local instance (φ : ℝ → ℝ) (s : ℝ) (q : ParentedScheduleNode) : Decidable (q.Visible φ s) := Classical.propDecidable _

def parentedHeight (φ : ℝ → ℝ) (P : ℝ) (q : ParentedScheduleNode) : ℝ :=
  nodeHeight φ P (q.node.source,q.node.reserve)

def parentWindowClear (φ : ℝ → ℝ) (P s : ℝ) (q : ParentedScheduleNode) : Prop :=
  match q.parent with
  | none => True
  | some p => P+Real.exp (parentedHeight φ P q+3*s) ≤ φ p.pivot

local instance (φ : ℝ → ℝ) (P s : ℝ) (q : ParentedScheduleNode) : Decidable (parentWindowClear φ P s q) := Classical.propDecidable _

def longVisibleNodes (φ : ℝ → ℝ) (P κ a b s : ℝ) (eligible : ℕ → ℝ → Bool) (t : ScheduleTree) : List ParentedScheduleNode :=
  (parentedNodes 0 κ none t).filter fun q => decide
    (P < φ q.node.pivot ∧ eligible q.node.pivotIndex q.node.pivot = true ∧
      a ≤ parentedHeight φ P q+s ∧ parentedHeight φ P q+2*s ≤ b ∧ parentWindowClear φ P s q)

theorem longVisibleNodes_window {φ : ℝ → ℝ} {P κ a b s : ℝ} {eligible : ℕ → ℝ → Bool} {t : ScheduleTree}
    {q : ParentedScheduleNode} (hq : q ∈ longVisibleNodes φ P κ a b s eligible t) :
    a ≤ parentedHeight φ P q+s ∧ parentedHeight φ P q+2*s ≤ b := by
  have hh := of_decide_eq_true (List.mem_filter.mp hq).2
  exact ⟨hh.2.2.1,hh.2.2.2.1⟩

/-- Every fixed-width visibility interval lies inside the actual range
where the node is an original full-cut gap. -/
theorem longVisibleNodes_visible {φ : ℝ → ℝ} {P κ a b s y : ℝ} {eligible : ℕ → ℝ → Bool} {t : ScheduleTree}
    {q : ParentedScheduleNode} (hs : 0 ≤ s) (hq : q ∈ longVisibleNodes φ P κ a b s eligible t)
    (hy : parentedHeight φ P q+s ≤ y ∧ y < parentedHeight φ P q+2*s) :
    q.Visible φ (P+Real.exp y) := by
  have hh := of_decide_eq_true (List.mem_filter.mp hq).2
  have hpos : 0 < φ q.node.pivot-P := sub_pos.mpr hh.1
  have hheight : Real.exp (parentedHeight φ P q) = φ q.node.pivot-P := Real.exp_log hpos
  have hroot := Real.exp_le_exp.mpr (show parentedHeight φ P q ≤ y by linarith only [hy.1,hs])
  rw [hheight] at hroot
  refine ⟨by linarith only [hroot],?_⟩
  have hp := hh.2.2.2.2
  cases he : q.parent with
  | none => trivial
  | some p =>
    have hp' : P+Real.exp (parentedHeight φ P q+3*s) ≤ φ p.pivot := by simpa only [parentWindowClear,he] using hp
    have he := Real.exp_lt_exp.mpr (show y < parentedHeight φ P q+3*s by linarith only [hy.2,hs])
    change P+Real.exp y < φ p.pivot
    linarith only [hp',he]

theorem parentedNodes_reserve_nonnegative {start : ℕ} {κ : ℝ} {parent : Option ScheduleNode}
    {t : ScheduleTree} {q : ParentedScheduleNode} (hκ : 0 ≤ κ) (hq : q ∈ parentedNodes start κ parent t) :
    0 ≤ q.node.reserve := by
  have he : q.node ∈ (parentedNodes start κ parent t).map ParentedScheduleNode.node := List.mem_map.mpr ⟨q,hq,rfl⟩
  rw [parentedNodes_erase] at he
  have hm : (q.node.source,q.node.reserve) ∈ (BinaryForest.labels (t.indexedTree start κ)).map (fun q => (q.source,q.reserve)) := List.mem_map.mpr ⟨q.node,he,rfl⟩
  rw [indexedTree_labels_reserves] at hm
  exact reservedNodes_reserve_nonnegative hκ hm

theorem visibleNodeScore_nonnegative (φ : ℝ → ℝ) {P : ℝ} (hP : 0 < P)
    (price : ℝ) (eligible : ℕ → ℝ → Bool) (q : ScheduleNode) (hκ : 0 ≤ q.reserve) :
    0 ≤ visibleNodeScore φ P price eligible q := by
  unfold visibleNodeScore
  split_ifs
  · exact add_nonneg (le_max_right _ _) (gapLogDeficit_nonnegative φ hP hκ _)
  · exact le_rfl

end
end StrongSilver
