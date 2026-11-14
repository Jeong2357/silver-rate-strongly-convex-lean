-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.GeometricLadder
import StrongSilver.AveragingScales
import StrongSilver.FinalAverageWindow
import StrongSilver.CounterexampleThresholds

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 1800000

/-- The stopping scale is constructed from the actual W/n and maximizing
threshold B of the counterexample schedule. -/
theorem CounterexampleSequence.eventually_geometric_ladder {a : ℝ} (S : CounterexampleSequence a) :
    ∀ᶠ j : ℕ in atTop,
      let Y := finalAverageLogScale (weightedCount (S.schedules j) (a*S.kappa j)/((S.schedules j).length : ℝ))
      let U := firstAverageLogScale (S.threshold j)
      ∃ m : ℕ, 1 ≤ m ∧ Y ≤ geometricScale U bandRatio m ∧ geometricScale U bandRatio m < bandRatio*Y ∧
        ∀ i ≤ m, Y ≤ geometricScale U bandRatio i ∧ geometricScale U bandRatio i ≤ U := by
  filter_upwards [S.ratio_escape.eventually_gt_atTop (1 : ℝ),S.threshold_escape.eventually_gt_atTop (1 : ℝ)]
    with j hR hB
  dsimp only
  let R := weightedCount (S.schedules j) (a*S.kappa j)/((S.schedules j).length : ℝ)
  have hR0 : 0 < R := zero_lt_one.trans hR
  have hB0 := zero_lt_one.trans hB
  have hν := nu_positive
  have hlogR := Real.log_le_log hR0 (S.ratio_le_threshold_power j)
  rw [Real.log_rpow hB0] at hlogR
  have hlogB := Real.log_pos hB
  have hY : 0 < finalAverageLogScale R := by
    unfold finalAverageLogScale
    exact div_pos (Real.log_pos hR) (by positivity)
  have hYB : finalAverageLogScale R ≤ Real.log (S.threshold j)/4 := by
    unfold finalAverageLogScale
    apply (div_le_iff₀ (show 0 < 4*nu by positivity)).mpr
    linear_combination hlogR
  have hrY := mul_le_mul_of_nonneg_right bandRatio_bounds.2.le hY.le
  have hη := mul_le_mul_of_nonneg_right firstAverageEta_bounds.2.le hlogB.le
  have hU : bandRatio*finalAverageLogScale R ≤ firstAverageLogScale (S.threshold j) := by
    unfold firstAverageLogScale
    nlinarith only [hrY,hYB,hη,hlogB]
  exact exists_geometric_ladder hY bandRatio_bounds.1 hU

end
end StrongSilver
