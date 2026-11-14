-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.IndexedBalancedEdgeSpacing
import StrongSilver.LabeledPruneProperties

namespace StrongSilver
open ScheduleTree BinaryForest
noncomputable section
set_option maxHeartbeats 4200000

theorem indexedTree_pivot_step_mem {start : ℕ} {κ : ℝ} {t : ScheduleTree} {q : ScheduleNode}
    (hq : q ∈ labels (indexedTree start κ t)) : q.pivot ∈ t.word := by
  have hh : (q.source,q.reserve) ∈ (labels (indexedTree start κ t)).map (fun q => (q.source,q.reserve)) :=
    List.mem_map.mpr ⟨q,hq,rfl⟩
  rw [indexedTree_labels_reserves] at hh
  exact reservedNodes_step_mem hh

/-- Pruning nonpositive selected factors keeps exactly the original
positive node occurrences, including repeated pivots at different positions. -/
theorem indexedTree_positive_prune_labels (φ : ℝ → ℝ) (hφ : Monotone φ) (P : ℝ)
    (start : ℕ) (κ : ℝ) (t : ScheduleTree) (hc : t.Cartesian) :
    labels (pruneBottom (fun q : ScheduleNode => φ q.pivot) P (indexedTree start κ t)) =
      (labels (indexedTree start κ t)).filter (fun q => decide (P < φ q.pivot)) := by
  induction t generalizing start κ with
  | leaf hw => rfl
  | split l b r il ir =>
    by_cases hp : P < φ b
    · have hhead : P < φ (⟨start,.split l b r,κ⟩ : ScheduleNode).pivot := hp
      simp only [indexedTree,pruneBottom,if_pos hhead,labels,List.filter_cons,decide_eq_true hhead,↓reduceIte,
        List.filter_append,il start 0 hc.1,ir _ κ hc.2.1]
    · have hnone : ((labels (indexedTree start κ (.split l b r))).filter (fun q => decide (P < φ q.pivot))) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro q hq
        exact Bool.eq_false_iff.mp (decide_eq_false (not_lt_of_ge ((hφ (split_word_le hc _ (indexedTree_pivot_step_mem hq))).trans (le_of_not_gt hp))))
      rw [hnone]
      have hhead : ¬ P < φ (⟨start,.split l b r,κ⟩ : ScheduleNode).pivot := hp
      simp only [indexedTree,pruneBottom,if_neg hhead,labels]

/-- Actual Cartesian pivot order supplies the upper-height hypothesis
on the retained positive subtree. -/
theorem indexedTree_positive_prune_below {φ : ℝ → ℝ} (hφ : Monotone φ) {P high κ : ℝ} {start : ℕ}
    (t : ScheduleTree) (hc : t.Cartesian) (hupper : φ t.rootStep ≤ P+Real.exp high) :
    labelsBelow (nodePaddedHeight φ P) high (pruneBottom (fun q : ScheduleNode => φ q.pivot) P (indexedTree start κ t)) := by
  rw [labelsBelow_iff,indexedTree_positive_prune_labels φ hφ P start κ t hc]
  intro q hq
  obtain ⟨hq,hpos⟩ := List.mem_filter.mp hq
  have hpositive : P < φ q.pivot := of_decide_eq_true hpos
  have hbound : φ q.pivot ≤ P+Real.exp high := by
    cases t with
    | leaf hw => simp [indexedTree,labels] at hq
    | split l b r =>
      have hh := hφ (split_word_le hc _ (indexedTree_pivot_step_mem hq))
      exact hh.trans hupper
  have hh := Real.log_le_log (sub_pos.mpr hpositive)
    (show φ q.pivot-P ≤ Real.exp high by linarith only [hbound])
  rw [Real.log_exp] at hh
  exact hh

end
end StrongSilver
