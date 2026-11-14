-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ActualParentMembership
import StrongSilver.ShortWindowEdges

namespace StrongSilver
open ScheduleTree ParentedScheduleNode
noncomputable section
set_option maxHeartbeats 4200000

def protectedWindowNodes (φ : ℝ → ℝ) (P κ a b : ℝ) (eligible : ℕ → ℝ → Bool) (t : ScheduleTree) : List ParentedScheduleNode :=
  (parentedNodes 0 κ none t).filter fun q => decide
    (P < φ q.node.pivot ∧ eligible q.node.pivotIndex q.node.pivot = true ∧
      a < parentedHeight φ P q ∧ parentedHeight φ P q+3*visibilitySpacing ≤ b)

/-- Every vertex in a protected window is either on a short actual
edge or has a full fixed-width visibility interval in the outer window. -/
theorem protected_node_short_or_long {φ : ℝ → ℝ} {P κ a b : ℝ} {eligible : ℕ → ℝ → Bool}
    {t : ScheduleTree} {q : ParentedScheduleNode}
    (hφ : Monotone φ) (hκ : 0 ≤ κ) (hc : t.Cartesian)
    (hq : q ∈ protectedWindowNodes φ P κ a b eligible t) :
    ShortWindowEdge φ P a b q ∨ q ∈ longVisibleNodes φ P κ a b visibilitySpacing eligible t := by
  classical
  obtain ⟨hmem,he⟩ := List.mem_filter.mp hq
  have H := of_decide_eq_true he
  obtain ⟨hroot,heligible,hlo,hhi⟩ := H
  have hs := visibilitySpacing_positive
  have hlong (hclear : parentWindowClear φ P visibilitySpacing q) :
      q ∈ longVisibleNodes φ P κ a b visibilitySpacing eligible t := by
    apply List.mem_filter.mpr
    exact ⟨hmem,decide_eq_true ⟨hroot,heligible,by linarith only [hlo,hs],by linarith only [hhi,hs],hclear⟩⟩
  cases hp : q.parent with
  | none => exact Or.inr (hlong (by simp only [parentWindowClear,hp]))
  | some p =>
    have hpMem := parentedNodes_parent_mem hmem hp
    have he := parentedNodes_actual_edge hmem hp
    have hpCart := indexedTree_source_cartesian hc hpMem
    have horder := actual_child_height_le hφ he hpCart hroot
    have hpκ := indexedTree_reserve_nonnegative hκ hpMem
    have hpRoot : P < φ p.pivot := hroot.trans_le (hφ (actual_child_pivot_le he hpCart))
    by_cases hshort : nodeHeight φ P (p.source,p.reserve)-parentedHeight φ P q < 3*visibilitySpacing
    · refine Or.inl ⟨p,hp,hpRoot,hpκ,hroot,?_,?_,hlo,?_,horder,hshort⟩
      · exact hlo.trans_le horder
      · linarith only [hshort,hhi]
      · linarith only [hhi,hs]
    · apply Or.inr
      apply hlong
      simp only [parentWindowClear,hp]
      have hh := Real.exp_le_exp.mpr (show parentedHeight φ P q+3*visibilitySpacing ≤ nodeHeight φ P (p.source,p.reserve) by linarith only [le_of_not_gt hshort])
      have hexp : Real.exp (nodeHeight φ P (p.source,p.reserve)) = φ p.pivot-P := Real.exp_log (sub_pos.mpr hpRoot)
      rw [hexp] at hh
      linarith only [hh]

end
end StrongSilver
