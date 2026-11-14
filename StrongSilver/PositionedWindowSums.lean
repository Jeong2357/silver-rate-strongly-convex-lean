-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PositionedWindowExcess
import StrongSilver.LongVisibleNodes
import StrongSilver.FiniteFilteredSums

namespace StrongSilver
open ScheduleTree
noncomputable section
set_option maxHeartbeats 3000000

/-- Any reserve-dependent observable has the same window sum on the
positioned occurrence list and the original reserved-node list. -/
theorem positioned_window_sum (φ : ℝ → ℝ) (P κ a b : ℝ) (t : ScheduleTree) (F : ScheduleTree × ℝ → ℝ) :
    ((parentedNodes 0 κ none t).map fun q =>
      if P < φ q.node.pivot ∧ a < parentedHeight φ P q ∧ parentedHeight φ P q ≤ b
      then F (q.node.source,q.node.reserve) else 0).sum =
      ((nodesInHeightWindow φ P κ a b t).map F).sum := by
  let f := fun q : ScheduleTree × ℝ =>
    if P < φ q.1.rootStep ∧ a < nodeHeight φ P q ∧ nodeHeight φ P q ≤ b then F q else 0
  have he := parentedNodes_sum_reserves f 0 κ none t
  change ((parentedNodes 0 κ none t).map fun q => f (q.node.source,q.node.reserve)).sum = ((nodesInHeightWindow φ P κ a b t).map F).sum
  rw [he]
  unfold nodesInHeightWindow positivePaddedNodes
  rw [list_filter_sum_eq,list_filter_sum_eq]
  congr 1
  apply List.map_congr_left
  intro q hq
  dsimp only [f]
  by_cases hp : P < φ q.1.rootStep <;> by_cases hw : a < nodeHeight φ P q ∧ nodeHeight φ P q ≤ b <;>
    simp only [hp,hw,decide_true,decide_false,Bool.false_eq_true,↓reduceIte,and_assoc,true_and,false_and,and_true,and_false,and_self,hw]

end
end StrongSilver
