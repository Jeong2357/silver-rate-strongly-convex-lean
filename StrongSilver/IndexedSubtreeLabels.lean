-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.IndexedScheduleTree

namespace StrongSilver.ScheduleTree
open BinaryForest
noncomputable section
set_option maxHeartbeats 4400000

/-- An indexed descendant carries its actual starting position and
reserve, so rebuilding its indexed subtree gives an original sublist. -/
theorem indexedTree_subtree_labels {start : ℕ} {κ : ℝ} {t : ScheduleTree} {q : ScheduleNode}
    (hq : q ∈ labels (t.indexedTree start κ)) :
    (labels (q.source.indexedTree q.start q.reserve)).Sublist (labels (t.indexedTree start κ)) := by
  induction t generalizing start κ with
  | leaf word => simp [indexedTree,labels] at hq
  | split l b r il ir =>
    simp only [indexedTree,labels,List.mem_cons,List.mem_append] at hq
    rcases hq with rfl | hl | hr
    · exact List.Sublist.refl _
    · have hsub := il hl
      exact hsub.trans ((List.sublist_append_left _ _).trans (List.sublist_cons_self _ _))
    · have hsub := ir hr
      exact hsub.trans ((List.sublist_append_right _ _).trans (List.sublist_cons_self _ _))

end
end StrongSilver.ScheduleTree
