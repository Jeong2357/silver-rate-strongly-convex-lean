-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ParentedScheduleNodes
import StrongSilver.FiniteFilteredSums

namespace StrongSilver
open ScheduleTree ParentedScheduleNode BinaryForest
noncomputable section
set_option maxHeartbeats 3400000

/-- Any selected visible occurrence may be charged to its actual
frontier gap. The proof uses the exact occurrence-list identity and
therefore preserves repeated equal steps and intervals. -/
theorem visible_occurrence_budget (φ : ℝ → ℝ) (hφ : Monotone φ) (s κ : ℝ)
    (t : ScheduleTree) (hc : t.Cartesian) (selected : ParentedScheduleNode → Bool)
    (cost : ParentedScheduleNode → ℝ) (gapCharge : ScheduleNode → ℝ) (hCharge : ∀ q, 0 ≤ gapCharge q)
    (hselected : ∀ q ∈ parentedNodes 0 κ none t, selected q = true →
      q.Visible φ s ∧ cost q ≤ gapCharge q.node) :
    (((parentedNodes 0 κ none t).filter selected).map cost).sum ≤
      ((indexedFrontier φ s 0 κ t).map gapCharge).sum := by
  classical
  have hDom := list_filtered_sum_domination selected (fun q => decide (q.Visible φ s)) cost
    (fun q => gapCharge q.node) (parentedNodes 0 κ none t) (fun q _ => hCharge q.node) (by
      intro q hq hs
      obtain ⟨hv,hc⟩ := hselected q hq hs
      exact ⟨decide_eq_true hv,hc⟩)
  have he := congrArg (fun qs : List ScheduleNode => (qs.map gapCharge).sum)
    (parentedNodes_visible φ hφ s 0 κ none t hc trivial)
  simp only [List.map_map,Function.comp_def] at he
  rw [he] at hDom
  have hsub : ((indexedFrontier φ s 0 κ t).filter internalNode).Sublist (indexedFrontier φ s 0 κ t) := List.filter_sublist
  have hF := (hsub.map gapCharge).sum_le_sum (by
    intro x hx
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hx
    exact hCharge q)
  exact hDom.trans hF

end
end StrongSilver
