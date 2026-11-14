-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.LinkedFrontier
import StrongSilver.ParentChargeMultiplicity
import StrongSilver.TreeRootOrder

namespace StrongSilver.ScheduleTree
open BinaryForest
noncomputable section
set_option maxHeartbeats 5400000

theorem indexedTree_pivot_mem_word {start : ℕ} {κ : ℝ} {t : ScheduleTree} {q : ScheduleNode}
    (hq : q ∈ labels (t.indexedTree start κ)) : q.pivot ∈ t.word := by
  induction t generalizing start κ with
  | leaf word => simp [indexedTree,labels] at hq
  | split l b r il ir =>
    simp only [indexedTree,labels,List.mem_cons,List.mem_append] at hq
    rcases hq with rfl | hl | hr
    · simp [word,ScheduleNode.pivot]
    · exact (left_word_sublist l r b).subset (il hl)
    · exact (right_word_sublist l r b).subset (ir hr)

theorem indexedTree_pivot_le_root {start : ℕ} {κ : ℝ} {t : ScheduleTree} {q : ScheduleNode}
    (hc : t.Cartesian) (hq : q ∈ labels (t.indexedTree start κ)) : q.pivot ≤ t.rootStep :=
  cartesian_word_le_root hc (indexedTree_pivot_mem_word hq)

/-- Every selected pivot follows exactly one chronological gap. The
external following boundary occurs once, at the end. This identity
counts indexed occurrences, including repeated pivot values. -/
theorem linkedFrontier_following_sum (φ : ℝ → ℝ) (hφ : Monotone φ) (s : ℝ) (F : ScheduleNode → ℝ)
    (start : ℕ) (κ : ℝ) (parent following : Option ScheduleNode) (t : ScheduleTree) (hc : t.Cartesian) :
    ((linkedFrontier φ s start κ parent following t).map fun q => optionalNodeCharge F q.following).sum =
      ((labels (t.indexedTree start κ)).map fun q => if s < φ q.pivot then F q else 0).sum+optionalNodeCharge F following := by
  induction t generalizing start κ parent following with
  | leaf word => simp [linkedFrontier,indexedTree,labels]
  | split l b r il ir =>
    by_cases hb : s < φ b
    · have hl := il start 0 (some (⟨start,.split l b r,κ⟩ : ScheduleNode)) (some (⟨start,.split l b r,κ⟩ : ScheduleNode)) hc.1
      have hr := ir (start+l.word.length+1) κ (some (⟨start,.split l b r,κ⟩ : ScheduleNode)) following hc.2.1
      rw [linkedFrontier,if_pos hb,List.map_append,List.sum_append,hl,hr]
      simp only [indexedTree,labels,List.map_cons,List.map_append,List.sum_cons,List.sum_append,optionalNodeCharge]
      have hroot : s < φ (⟨start,.split l b r,κ⟩ : ScheduleNode).pivot := hb
      rw [if_pos hroot]
      ring
    · have hzero : ((labels ((ScheduleTree.split l b r).indexedTree start κ)).map fun q => if s < φ q.pivot then F q else 0).sum = 0 := by
        apply List.sum_eq_zero
        intro x hx
        obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hx
        have hh := hφ (indexedTree_pivot_le_root hc hq)
        have hnot : ¬ s < φ q.pivot := not_lt_of_ge (hh.trans (le_of_not_gt hb))
        exact if_neg hnot
      rw [hzero,zero_add,linkedFrontier,if_neg hb]
      simp only [List.map_singleton,List.sum_singleton]

end
end StrongSilver.ScheduleTree
