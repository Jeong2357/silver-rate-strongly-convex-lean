-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.LinkedFrontier
import StrongSilver.LinkedFollowingProperties
import StrongSilver.FrontierRootUpper
import StrongSilver.IndexedPositivePrune
import StrongSilver.TreeRootOrder

namespace StrongSilver
open ScheduleTree BinaryForest
noncomputable section
set_option maxHeartbeats 5200000

theorem list_sum_map_flatMap {α β : Type*} (f : α → List β) (F : β → ℝ) (xs : List α) :
    ((xs.flatMap f).map F).sum = (xs.map fun x => ((f x).map F).sum).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons,List.map_append,List.sum_append,List.map_cons,List.sum_cons,ih]


/-- The disjoint original source subtrees of all actual cut gaps
contain exactly the unselected original internal occurrences. -/
theorem indexedFrontier_subtree_labels (φ : ℝ → ℝ) (hφ : Monotone φ) (s : ℝ)
    (start : ℕ) (κ : ℝ) (t : ScheduleTree) (hc : t.Cartesian) :
    ((indexedFrontier φ s start κ t).flatMap fun q => labels (q.source.indexedTree q.start q.reserve)) =
      (labels (t.indexedTree start κ)).filter (fun q => decide (φ q.pivot ≤ s)) := by
  induction t generalizing start κ with
  | leaf word => simp [indexedFrontier,indexedTree,labels]
  | split l b r il ir =>
    by_cases hb : s < φ b
    · simp only [indexedFrontier,if_pos hb,List.flatMap_append,il _ _ hc.1,ir _ _ hc.2.1,
        indexedTree,labels,List.filter_cons,ScheduleNode.pivot,rootStep_split,
        decide_eq_true_eq,List.filter_append]
      split_ifs with hflag
      · exact False.elim ((not_le_of_gt hb) (of_decide_eq_true hflag))
      · rfl
    · have hAll : ∀ q ∈ labels ((ScheduleTree.split l b r).indexedTree start κ), φ q.pivot ≤ s := by
        intro q hq
        have hh := hφ (cartesian_word_le_root hc (indexedTree_pivot_step_mem hq))
        exact hh.trans (le_of_not_gt hb)
      simp only [indexedFrontier,if_neg hb,List.flatMap_cons,List.flatMap_nil,List.append_nil]
      symm
      exact List.filter_eq_self.mpr (fun q hq => decide_eq_true (hAll q hq))

theorem linkedFrontier_subtree_labels (φ : ℝ → ℝ) (hφ : Monotone φ) (s : ℝ)
    (start : ℕ) (κ : ℝ) (parent following : Option ScheduleNode) (t : ScheduleTree) (hc : t.Cartesian) :
    ((linkedFrontier φ s start κ parent following t).flatMap fun q =>
      labels (q.node.source.indexedTree q.node.start q.node.reserve)) =
      (labels (t.indexedTree start κ)).filter (fun q => decide (φ q.pivot ≤ s)) := by
  have hh := congrArg (fun qs : List ScheduleNode => qs.flatMap fun q => labels (q.source.indexedTree q.start q.reserve))
    (linkedFrontier_erase φ s start κ parent following t)
  rw [List.flatMap_map] at hh
  exact hh.trans (indexedFrontier_subtree_labels φ hφ s start κ t hc)

/-- Nonnegative per-occurrence charges on disjoint frontier subtrees
can be paid by the original global occurrence list once. -/
theorem linkedFrontier_subtree_sum_le (φ : ℝ → ℝ) (hφ : Monotone φ) (s : ℝ)
    (start : ℕ) (κ : ℝ) (parent following : Option ScheduleNode) (t : ScheduleTree) (hc : t.Cartesian)
    (F : ScheduleNode → ℝ) (hF : ∀ q, 0 ≤ F q) :
    ((linkedFrontier φ s start κ parent following t).map fun q =>
      ((labels (q.node.source.indexedTree q.node.start q.node.reserve)).map F).sum).sum ≤
      ((labels (t.indexedTree start κ)).map F).sum := by
  have hh := congrArg (fun qs : List ScheduleNode => (qs.map F).sum)
    (linkedFrontier_subtree_labels φ hφ s start κ parent following t hc)
  rw [list_sum_map_flatMap] at hh
  rw [hh]
  apply (List.filter_sublist.map F).sum_le_sum
  intro x hx
  obtain ⟨q,_,rfl⟩ := List.mem_map.mp hx
  exact hF q

end
end StrongSilver
