-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ProtectedWindowNodes

namespace StrongSilver
open ScheduleTree
noncomputable section
set_option maxHeartbeats 3000000

theorem protected_node_window_excess {φ : ℝ → ℝ} {P κ a b : ℝ} {eligible : ℕ → ℝ → Bool}
    {t : ScheduleTree} {q : ParentedScheduleNode} (hκ : 0 ≤ κ)
    (hq : q ∈ protectedWindowNodes φ P κ a b eligible t) :
    windowNodeExcess φ P a b q.node = nodeExcess φ P (q.node.source,q.node.reserve) := by
  have H := of_decide_eq_true (List.mem_filter.mp hq).2
  have hres := parentedNodes_reserve_nonnegative hκ (List.mem_filter.mp hq).1
  apply if_pos
  refine ⟨H.1,hres,H.2.2.1,?_⟩
  change parentedHeight φ P q ≤ b
  linarith only [H.2.2.2,visibilitySpacing_positive]

theorem protected_excess_le_window {φ : ℝ → ℝ} {P κ a b : ℝ} (hP : 0 < P) (hκ : 0 ≤ κ) (hzero : φ 0 ≤ 0)
    (eligible : ℕ → ℝ → Bool) (t : ScheduleTree) :
    ((protectedWindowNodes φ P κ a b eligible t).map fun q => nodeExcess φ P (q.node.source,q.node.reserve)).sum ≤
      ((parentedNodes 0 κ none t).map fun q => windowNodeExcess φ P a b q.node).sum := by
  have he : ((protectedWindowNodes φ P κ a b eligible t).map fun q => nodeExcess φ P (q.node.source,q.node.reserve)).sum =
      ((protectedWindowNodes φ P κ a b eligible t).map fun q => windowNodeExcess φ P a b q.node).sum := by
    congr 1
    apply List.map_congr_left
    intro q hq
    exact (protected_node_window_excess hκ hq).symm
  rw [he]
  have hsub : (protectedWindowNodes φ P κ a b eligible t).Sublist (parentedNodes 0 κ none t) := List.filter_sublist
  apply (hsub.map (fun q => windowNodeExcess φ P a b q.node)).sum_le_sum
  intro x hx
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hx
  exact windowNodeExcess_nonnegative φ hP hzero a b q.node

end
end StrongSilver
