-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.IndexedWindowExactLabels
import StrongSilver.FiniteFilteredSums

namespace StrongSilver
open ScheduleTree BinaryForest
noncomputable section
set_option maxHeartbeats 4200000

/-- The scalar gains on all original vertices of a cutoff refinement
sum to its exact logarithmic saving, with absolute original indices. -/
theorem indexed_window_log_saving {φ : ℝ → ℝ} (hφ : StrictMono φ) {P κ low A : ℝ}
    (hP : 0 < P) (hκ : 0 ≤ κ) (hA : 0 ≤ A) (hcut : φ A = P+Real.exp low)
    (start : ℕ) (t : ScheduleTree) (hc : t.Cartesian) :
    ((labels (indexedHeightWindow φ P low start κ t)).map fun q => paddedRootGain φ P q.reserve q.source).sum =
      Real.log (gapPrefix φ t.word+P+κ)-
        cutLogProduct φ P κ (cutScheduleFrom (fun _ b => decide (A < b)) start t.word) := by
  have hiff (q : ScheduleNode) : (P < φ q.pivot ∧ low < nodePaddedHeight φ P q) ↔ A < q.pivot := by
    constructor
    · intro hh
      have he := (Real.lt_log_iff_exp_lt (sub_pos.mpr hh.1)).mp hh.2
      apply hφ.lt_iff_lt.mp
      rw [hcut]
      linarith only [he]
    · intro hh
      have he := hφ hh
      rw [hcut] at he
      have hp : P < φ q.pivot := by have hx := Real.exp_pos low; linarith only [he,hx]
      refine ⟨hp,?_⟩
      exact (Real.lt_log_iff_exp_lt (sub_pos.mpr hp)).mpr (by linarith only [he])
  rw [indexed_height_window_labels φ hφ.monotone P low start κ t hc,list_filter_sum_eq]
  simp only [hiff,decide_eq_true_eq]
  let F := fun q : ScheduleTree × ℝ => if A < q.1.rootStep then paddedRootGain φ P q.2 q.1 else 0
  have hmap := congrArg (fun qs : List (ScheduleTree × ℝ) => (qs.map F).sum) (indexedTree_labels_reserves start κ t)
  simp only [List.map_map,Function.comp_def] at hmap
  change ((labels (indexedTree start κ t)).map fun q => F (q.source,q.reserve)).sum = _
  rw [hmap]
  rw [← splitSumAbove_eq_node_sum (fun reserve source => paddedRootGain φ P reserve source) A κ t hc]
  have hlog := full_cut_log_jump_formula (φ := φ) hP hκ hA t hc (by
    intro b hb hAb
    have he := hφ hAb
    rw [hcut] at he
    have hx := Real.exp_pos low
    linarith only [he,hx]) start
  linear_combination hlog

end
end StrongSilver
