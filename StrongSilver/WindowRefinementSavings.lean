-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.IndexedWindowCutCount
import StrongSilver.IndexedWindowLogSaving
import StrongSilver.ArbitraryGapRefinement

namespace StrongSilver
open ScheduleTree BinaryForest
noncomputable section
set_option maxHeartbeats 4200000

/-- Refining an actual gap by every eligible vertex in the cutoff-height
window is a finite competitor for R_I. Its logarithmic gains telescope
exactly and its insertion count is the actual pruned-tree node count. -/
theorem window_gain_le_gap_savings {φ : ℝ → ℝ} (hφ : StrictMono φ) {P κ low A price : ℝ}
    (hP : 0 < P) (hκ : 0 ≤ κ) (hzero : φ 0 ≤ P) (hA : 0 ≤ A) (hcut : φ A = P+Real.exp low)
    (start : ℕ) (t : ScheduleTree) (hc : t.Cartesian) (eligible : ℕ → ℝ → Bool)
    (hEligible : ∀ j : ℕ, ∀ b ∈ t.word, A < b → eligible j b = true) :
    ((labels (indexedHeightWindow φ P low start κ t)).map fun q => paddedRootGain φ P q.reserve q.source).sum ≤
      gapSavingsMaximum φ P κ price start t.word eligible+price*((indexedHeightWindow φ P low start κ t).numNodes:ℝ) := by
  have hScore := gap_refinement_score_le_maximum φ P κ price start t.word eligible
    (fun _ b => decide (A < b)) (by
      intro p hp
      exact hEligible (start+p.val) t.word[p] (List.getElem_mem p.isLt) (of_decide_eq_true hp))
  have hCount := indexed_height_window_cut_count (κ := κ) (low := low) φ hφ.monotone hzero start t hc
  have heq : (fun (_ : ℕ) b => decide (P+Real.exp low < φ b)) = (fun (_ : ℕ) b => decide (A < b)) := by
    funext j b
    rw [← hcut]
    simp only [hφ.lt_iff_lt]
  rw [heq] at hCount
  have hLog := indexed_window_log_saving hφ hP hκ hA hcut start t hc
  unfold gapRefinementScore at hScore
  rw [← hCount,← hLog] at hScore
  linarith only [hScore]

end
end StrongSilver
