-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.IndexedScheduleTree
import StrongSilver.ScheduleCutSublist

namespace StrongSilver.ScheduleTree
open BinaryForest
noncomputable section
set_option maxHeartbeats 3400000

theorem indexedTree_pivot_indices_nodup (start : ℕ) (κ : ℝ) (t : ScheduleTree) :
    ((labels (t.indexedTree start κ)).map ScheduleNode.pivotIndex).Nodup := by
  induction t generalizing start κ with
  | leaf hw => simp [indexedTree,labels]
  | split l b r il ir =>
    have hL : ∀ i ∈ (labels (l.indexedTree start 0)).map ScheduleNode.pivotIndex,
        i < start+l.word.length := by
      intro i hi
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hi
      exact (indexedTree_pivot_bounds hq).2
    have hR : ∀ i ∈ (labels (r.indexedTree (start+l.word.length+1) κ)).map ScheduleNode.pivotIndex,
        start+l.word.length < i := by
      intro i hi
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hi
      have hh := (indexedTree_pivot_bounds hq).1
      omega
    simp only [indexedTree,labels,List.map_cons,List.map_append]
    change ((start+l.word.length) ::
      ((labels (l.indexedTree start 0)).map ScheduleNode.pivotIndex++
        (labels (r.indexedTree (start+l.word.length+1) κ)).map ScheduleNode.pivotIndex)).Nodup
    apply List.nodup_cons.mpr
    constructor
    · intro hm
      rcases List.mem_append.mp hm with hm | hm
      · have hh := hL _ hm; omega
      · have hh := hR _ hm; omega
    · apply List.nodup_append.mpr
      refine ⟨il start 0,ir (start+l.word.length+1) κ,?_⟩
      intro i hiL j hjR heq
      have hhL := hL i hiL
      have hhR := hR j hjR
      omega

/-- A weighted node sum is bounded by the original signed word sum.
This direct occurrence sum avoids treating equal steps as distinct values. -/
theorem indexedTree_pivot_weight_le_word (w : ℝ → ℝ) (hw : ∀ b, 0 ≤ w b)
    (start : ℕ) (κ : ℝ) (t : ScheduleTree) :
    ((labels (t.indexedTree start κ)).map fun q => w q.pivot).sum ≤ (t.word.map w).sum := by
  induction t generalizing start κ with
  | leaf h =>
    change 0 ≤ (h.map w).sum
    apply List.sum_nonneg
    intro x hx
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx
    exact hw b
  | split l b r il ir =>
    have hl := il start 0
    have hr := ir (start+l.word.length+1) κ
    have hhead : (⟨start,.split l b r,κ⟩ : ScheduleNode).pivot = b := rfl
    simp only [indexedTree,labels,List.map_cons,List.map_append,List.sum_cons,List.sum_append,word,hhead]
    linear_combination hl+hr

end
end StrongSilver.ScheduleTree
