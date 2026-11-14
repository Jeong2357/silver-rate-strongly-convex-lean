-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.IndexedWindowNodeBound

namespace StrongSilver
open ScheduleTree BinaryForest
noncomputable section
set_option maxHeartbeats 5200000

/-- The double pruning keeps exactly the positive original occurrences
whose logarithmic heights exceed the lower window boundary. -/
theorem indexed_height_window_labels (φ : ℝ → ℝ) (hφ : Monotone φ) (P low : ℝ)
    (start : ℕ) (κ : ℝ) (t : ScheduleTree) (hc : t.Cartesian) :
    labels (indexedHeightWindow φ P low start κ t) =
      (labels (indexedTree start κ t)).filter (fun q => decide (P < φ q.pivot ∧ low < nodePaddedHeight φ P q)) := by
  induction t generalizing start κ with
  | leaf hw => rfl
  | split l b r il ir =>
    let root : ScheduleNode := ⟨start,.split l b r,κ⟩
    by_cases hp : P < φ b
    · by_cases hy : low < Real.log (φ b-P)
      · have hp' : P < φ root.pivot := hp
        have hy' : low < nodePaddedHeight φ P root := hy
        have hBoth : P < φ root.pivot ∧ low < nodePaddedHeight φ P root := ⟨hp',hy'⟩
        change labels (pruneBottom (nodePaddedHeight φ P) low
          (pruneBottom (fun q : ScheduleNode => φ q.pivot) P
            (BinaryTree.node root (indexedTree start 0 l) (indexedTree (start+l.word.length+1) κ r)))) =
          (root::(labels (indexedTree start 0 l)++labels (indexedTree (start+l.word.length+1) κ r))).filter
            (fun q => decide (P < φ q.pivot ∧ low < nodePaddedHeight φ P q))
        rw [pruneBottom,if_pos hp',pruneBottom,if_pos hy',labels,List.filter_cons,
          decide_eq_true hBoth,if_pos rfl,List.filter_append]
        change root::(labels (indexedHeightWindow φ P low start 0 l)++labels (indexedHeightWindow φ P low (start+l.word.length+1) κ r)) = _
        rw [il start 0 hc.1,ir _ κ hc.2.1]
      · have hp' : P < φ root.pivot := hp
        have hy' : ¬ low < nodePaddedHeight φ P root := hy
        have hnone : ((labels (indexedTree start κ (.split l b r))).filter
            (fun q => decide (P < φ q.pivot ∧ low < nodePaddedHeight φ P q))) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro q hq
          apply Bool.eq_false_iff.mp
          apply decide_eq_false
          intro hh
          have hqpos := hh.1
          have hm := hφ (split_word_le hc _ (indexedTree_pivot_step_mem hq))
          have hlog := Real.log_le_log (sub_pos.mpr hqpos) (sub_le_sub_right hm P)
          have hnode : nodePaddedHeight φ P q ≤ Real.log (φ b-P) := hlog
          exact hy (hh.2.trans_le hnode)
        rw [hnone]
        change labels (pruneBottom (nodePaddedHeight φ P) low
          (pruneBottom (fun q : ScheduleNode => φ q.pivot) P (BinaryTree.node root _ _))) = []
        simp only [pruneBottom,if_pos hp',if_neg hy',labels]
    · have hp' : ¬ P < φ root.pivot := hp
      have hnone : ((labels (indexedTree start κ (.split l b r))).filter
          (fun q => decide (P < φ q.pivot ∧ low < nodePaddedHeight φ P q))) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro q hq
        apply Bool.eq_false_iff.mp
        apply decide_eq_false
        intro hh
        have hm := hφ (split_word_le hc _ (indexedTree_pivot_step_mem hq))
        exact hp (hh.1.trans_le hm)
      rw [hnone]
      change labels (pruneBottom (nodePaddedHeight φ P) low
        (pruneBottom (fun q : ScheduleNode => φ q.pivot) P (BinaryTree.node root _ _))) = []
      simp only [pruneBottom,if_neg hp',labels]

end
end StrongSilver
