-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.LinkedFrontier
import StrongSilver.FiniteFilteredSums

namespace StrongSilver.ScheduleTree
noncomputable section
set_option maxHeartbeats 4800000

/-- Equality of original linked-frontier and parented-occurrence sums
when leaf and hidden occurrences have zero score. -/
theorem linkedFrontier_sum_visible (φ : ℝ → ℝ) (hφ : Monotone φ) (s : ℝ)
    (start : ℕ) (κ : ℝ) (parent following : Option ScheduleNode) (t : ScheduleTree)
    (hc : t.Cartesian) (hp : ParentedScheduleNode.parentAbove φ s parent)
    (F : ParentedScheduleNode → ℝ)
    (hLeaf : ∀ q ∈ linkedFrontier φ s start κ parent following t, internalNode q.node ≠ true → F q.toParented = 0)
    (hHidden : ∀ q ∈ parentedNodes start κ parent t, ¬ q.Visible φ s → F q = 0) :
    ((linkedFrontier φ s start κ parent following t).map fun q => F q.toParented).sum =
      ((parentedNodes start κ parent t).map F).sum := by
  classical
  let xs := linkedFrontier φ s start κ parent following t
  let ys := parentedNodes start κ parent t
  have h1 : (xs.map fun q => F q.toParented).sum =
      ((xs.filter fun q => internalNode q.node).map fun q => F q.toParented).sum := by
    rw [list_filter_sum_eq]
    congr 1
    apply List.map_congr_left
    intro q hq
    by_cases hqI : internalNode q.node = true
    · simp only [hqI,↓reduceIte]
    · simp only [if_neg hqI,hLeaf q hq hqI]
  have h2 : ((xs.filter fun q => internalNode q.node).map fun q => F q.toParented).sum =
      ((ys.filter fun q => @decide (q.Visible φ s) (Classical.propDecidable _)).map F).sum := by
    have H := congrArg (fun qs : List ParentedScheduleNode => (qs.map F).sum)
      (linkedFrontier_internal_parented φ hφ s start κ parent following t hc hp)
    simpa only [List.map_map,Function.comp_def] using H
  have h3 : ((ys.filter fun q => @decide (q.Visible φ s) (Classical.propDecidable _)).map F).sum = (ys.map F).sum := by
    rw [list_filter_sum_eq]
    congr 1
    apply List.map_congr_left
    intro q hq
    by_cases hv : q.Visible φ s
    · simp only [decide_eq_true hv,↓reduceIte]
    · simp only [decide_eq_false hv,Bool.false_eq_true,↓reduceIte,hHidden q hq hv]
  exact h1.trans (h2.trans h3)

end
end StrongSilver.ScheduleTree
