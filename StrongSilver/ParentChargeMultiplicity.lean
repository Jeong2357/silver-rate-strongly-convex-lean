-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ParentedScheduleNodes

namespace StrongSilver
open ScheduleTree
noncomputable section
set_option maxHeartbeats 2600000

def optionalNodeCharge (F : ScheduleNode → ℝ) : Option ScheduleNode → ℝ
  | none => 0
  | some q => F q

theorem optionalNodeCharge_nonnegative (F : ScheduleNode → ℝ) (hF : ∀ q, 0 ≤ F q) (parent : Option ScheduleNode) :
    0 ≤ optionalNodeCharge F parent := by
  cases parent with
  | none => exact le_rfl
  | some q => exact hF q

/-- Each internal parent has at most two immediate internal children.
The estimate counts occurrences and allows arbitrary nonnegative charges. -/
theorem parent_charge_multiplicity (F : ScheduleNode → ℝ) (hF : ∀ q, 0 ≤ F q)
    (start : ℕ) (κ : ℝ) (parent : Option ScheduleNode) (t : ScheduleTree) :
    ((parentedNodes start κ parent t).map fun q => optionalNodeCharge F q.parent).sum ≤
      2*((parentedNodes start κ parent t).map fun q => F q.node).sum+optionalNodeCharge F parent := by
  induction t generalizing start κ parent with
  | leaf hw =>
    simpa only [parentedNodes,List.map_nil,List.sum_nil,mul_zero,zero_add] using optionalNodeCharge_nonnegative F hF parent
  | split l b r il ir =>
    have hl := il start 0 (some (⟨start,.split l b r,κ⟩ : ScheduleNode))
    have hr := ir (start+l.word.length+1) κ (some (⟨start,.split l b r,κ⟩ : ScheduleNode))
    simp only [parentedNodes,List.map_cons,List.map_append,List.sum_cons,List.sum_append,optionalNodeCharge] at hl hr ⊢
    linear_combination hl+hr

theorem parent_charge_multiplicity_root (F : ScheduleNode → ℝ) (hF : ∀ q, 0 ≤ F q) (κ : ℝ) (t : ScheduleTree) :
    ((parentedNodes 0 κ none t).map fun q => optionalNodeCharge F q.parent).sum ≤
      2*((parentedNodes 0 κ none t).map fun q => F q.node).sum := by
  simpa only [optionalNodeCharge,add_zero] using parent_charge_multiplicity F hF 0 κ none t

end
end StrongSilver
