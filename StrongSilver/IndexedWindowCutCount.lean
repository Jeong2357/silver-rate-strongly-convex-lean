-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.IndexedWindowExactLabels

namespace StrongSilver
open ScheduleTree BinaryForest
noncomputable section
set_option maxHeartbeats 4200000

/-- The nodes retained in an actual logarithmic window are exactly the
pivots inserted by the corresponding original-word threshold cut. -/
theorem indexed_height_window_cut_count (φ : ℝ → ℝ) (hφ : Monotone φ) {P low κ : ℝ}
    (hzero : φ 0 ≤ P) (start : ℕ) (t : ScheduleTree) (hc : t.Cartesian) :
    (indexedHeightWindow φ P low start κ t).numNodes =
      (cutScheduleFrom (fun _ b => decide (P+Real.exp low < φ b)) start t.word).phases.length := by
  induction t generalizing start κ with
  | leaf hw =>
    have hn : ∀ b ∈ hw, ∀ j : ℕ, decide (P+Real.exp low < φ b) = false := by
      intro b hb j
      have he := Real.exp_pos low
      exact decide_eq_false (by have hh := (hφ (hc b hb)).trans hzero; linarith only [hh,he])
    rw [word,cutScheduleFrom_none _ start hw hn]
    rfl
  | split l b r il ir =>
    by_cases hb : P+Real.exp low < φ b
    · have hpos : P < φ b := by have he := Real.exp_pos low; linarith only [hb,he]
      have hh : low < Real.log (φ b-P) := (Real.lt_log_iff_exp_lt (sub_pos.mpr hpos)).mpr (by linarith only [hb])
      let q : ScheduleNode := ⟨start,.split l b r,κ⟩
      have hpos' : P < φ q.pivot := hpos
      have hh' : low < nodePaddedHeight φ P q := hh
      change (pruneBottom (nodePaddedHeight φ P) low (pruneBottom (fun q : ScheduleNode => φ q.pivot) P
        (BinaryTree.node q (indexedTree start 0 l) (indexedTree (start+l.word.length+1) κ r)))).numNodes = _
      rw [pruneBottom,if_pos hpos',pruneBottom,if_pos hh']
      rw [BinaryTree.numNodes]
      change (indexedHeightWindow φ P low start 0 l).numNodes+
        (indexedHeightWindow φ P low (start+l.word.length+1) κ r).numNodes+1 = _
      rw [il (κ := 0) start hc.1,ir (κ := κ) _ hc.2.1,word,cutScheduleFrom_append]
      simp only [cutScheduleFrom,decide_eq_true hb,↓reduceIte,ScheduleCut.concat_before_selected,List.length_append,List.length_cons]
      omega
    · have hall : ∀ x ∈ (.split l b r : ScheduleTree).word, φ x ≤ P+Real.exp low :=
        fun x hx => (hφ (split_word_le hc x hx)).trans (le_of_not_gt hb)
      have hn : ∀ x ∈ (.split l b r : ScheduleTree).word, ∀ j : ℕ, decide (P+Real.exp low < φ x) = false :=
        fun x hx _ => decide_eq_false (not_lt_of_ge (hall x hx))
      rw [cutScheduleFrom_none _ start _ hn]
      have hz : (labels (indexedHeightWindow φ P low start κ (.split l b r))).length = 0 := by
        rw [indexed_height_window_labels φ hφ P low start κ _ hc]
        have hnil : ((labels (indexedTree start κ (.split l b r))).filter
            (fun q => decide (P < φ q.pivot ∧ low < nodePaddedHeight φ P q))) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro q hq
          apply Bool.eq_false_iff.mp
          apply decide_eq_false
          intro hq'
          have hheight := (Real.lt_log_iff_exp_lt (sub_pos.mpr hq'.1)).mp hq'.2
          have hdom := hall q.pivot (indexedTree_pivot_step_mem hq)
          linarith only [hheight,hdom]
        rw [hnil]
        rfl
      rw [labels_length] at hz
      exact hz

end
end StrongSilver
