-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.WeightedCountProperties
import StrongSilver.CappedPivotMoments
import StrongSilver.ScheduleCutSublist

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 1600000

theorem countAbove_sublist_le {g h : List ℝ} (hsub : g.Sublist h) (s : ℝ) : countAbove g s ≤ countAbove h s := by
  exact (hsub.filter (fun b => decide (s ≤ b))).length_le

theorem weightedCount_sublist_le {g h : List ℝ} (hsub : g.Sublist h) (cap : ℝ) :
    weightedCount g cap ≤ weightedCount h cap := by
  apply weightedCount_le g cap _ (weightedCount_nonneg h cap)
  intro s hs hcap
  have hc : (countAbove g s : ℝ) ≤ (countAbove h s : ℝ) := by exact_mod_cast countAbove_sublist_le hsub s
  have hh := mul_le_mul_of_nonneg_left hc (Real.rpow_pos_of_pos hs nu).le
  exact hh.trans (by simpa only [mul_comm] using threshold_le_weightedCount h hs hcap)

end
end StrongSilver
