-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.LinkedParentMembership

namespace StrongSilver.ScheduleTree
open BinaryForest
noncomputable section
set_option maxHeartbeats 6400000

/-- Frontier gaps whose parent was already selected at the top cut are
among the gaps present at that cut. Lowering the cut can only remove
such gaps, replacing them by children of newly selected parents. -/
theorem frozen_frontier_count (φ : ℝ → ℝ) (hφ : Monotone φ) {s top : ℝ} (hst : s ≤ top)
    (start : ℕ) (κ : ℝ) (parent following : Option ScheduleNode) (t : ScheduleTree) (hc : t.Cartesian) :
    ((linkedFrontier φ s start κ parent following t).filter fun q =>
      @decide (ParentedScheduleNode.parentAbove φ top q.parent) (Classical.propDecidable _)).length ≤
      (indexedFrontier φ top start κ t).length := by
  classical
  induction t generalizing start κ parent following with
  | leaf word =>
    exact (List.length_filter_le _ _).trans_eq (by rfl)
  | split l b r il ir =>
    by_cases hb : s < φ b
    · by_cases htop : top < φ b
      · have hl := il start 0 (some (⟨start,.split l b r,κ⟩ : ScheduleNode)) (some (⟨start,.split l b r,κ⟩ : ScheduleNode)) hc.1
        have hr := ir (start+l.word.length+1) κ (some (⟨start,.split l b r,κ⟩ : ScheduleNode)) following hc.2.1
        simp only [linkedFrontier,if_pos hb,List.filter_append,List.length_append,indexedFrontier,if_pos htop]
        exact Nat.add_le_add hl hr
      · have hroot : φ (⟨start,.split l b r,κ⟩ : ScheduleNode).pivot ≤ top := le_of_not_gt htop
        have hExternal : ¬ ParentedScheduleNode.parentAbove φ top (some (⟨start,.split l b r,κ⟩ : ScheduleNode)) := not_lt_of_ge hroot
        have hLnodes : ∀ p ∈ labels (l.indexedTree start 0), φ p.pivot ≤ top := by
          intro p hp
          have hMem : p ∈ labels ((ScheduleTree.split l b r).indexedTree start κ) := by
            simp only [indexedTree,labels,List.mem_cons,List.mem_append]
            exact Or.inr (Or.inl hp)
          exact (hφ (indexedTree_pivot_le_root hc hMem)).trans (le_of_not_gt htop)
        have hRnodes : ∀ p ∈ labels (r.indexedTree (start+l.word.length+1) κ), φ p.pivot ≤ top := by
          intro p hp
          have hMem : p ∈ labels ((ScheduleTree.split l b r).indexedTree start κ) := by
            simp only [indexedTree,labels,List.mem_cons,List.mem_append]
            exact Or.inr (Or.inr hp)
          exact (hφ (indexedTree_pivot_le_root hc hMem)).trans (le_of_not_gt htop)
        have hLn : ((linkedFrontier φ s start 0 (some (⟨start,.split l b r,κ⟩ : ScheduleNode))
            (some (⟨start,.split l b r,κ⟩ : ScheduleNode)) l).filter fun q =>
            decide (ParentedScheduleNode.parentAbove φ top q.parent)) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro q hq
          exact Bool.eq_false_iff.mp (decide_eq_false (linkedFrontier_no_parent_above hExternal hLnodes hq))
        have hRn : ((linkedFrontier φ s (start+l.word.length+1) κ (some (⟨start,.split l b r,κ⟩ : ScheduleNode))
            following r).filter fun q => decide (ParentedScheduleNode.parentAbove φ top q.parent)) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro q hq
          exact Bool.eq_false_iff.mp (decide_eq_false (linkedFrontier_no_parent_above hExternal hRnodes hq))
        rw [linkedFrontier,if_pos hb,List.filter_append,hLn,hRn]
        simp only [List.nil_append,List.length_nil,Nat.zero_le]
    · have hn : ¬ top < φ b := not_lt_of_ge ((le_of_not_gt hb).trans hst)
      rw [linkedFrontier,if_neg hb,indexedFrontier,if_neg hn]
      exact List.length_filter_le _ _

end
end StrongSilver.ScheduleTree
