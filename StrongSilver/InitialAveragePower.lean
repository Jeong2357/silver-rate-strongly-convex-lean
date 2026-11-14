-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FirstThresholdPower
import StrongSilver.AveragingScales
import StrongSilver.AveragedCutPower

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 1800000

/-- The actual first averaged power is at least c*W, for a curvature whose
quarter-scale inverse charge is retained for the later band estimates. -/
theorem CounterexampleSequence.eventually_initial_average_lower {a : ℝ} (ha : 0 < a) (hamax : a ≤ 1/128)
    (htrack : 7*initialMarkedLogCoefficient a ≤ 1/2)
    (herror : 2*splitCoefficient*initialStableErrorCoefficient a ≤ powerLogMinimum/16)
    (S : CounterexampleSequence a) : ∀ᶠ j : ℕ in atTop,
    ∃ μ : ℝ, 1/S.kappa j ≤ μ ∧ μ ≤ 9/(8*S.kappa j) ∧ (∀ b ∈ S.schedules j, 1-μ*b ≠ 0) ∧
      inverseChargeAbove (S.kappa j/4) (S.schedules j) μ ≤ 34*(countAbove (S.schedules j) (S.kappa j/4) : ℝ) ∧
      (powerLogMinimum/16)*weightedCount (S.schedules j) (a*S.kappa j) ≤
        averagedCutPower (cappedStep μ (S.threshold j)) (S.kappa j) (S.schedules j) (firstAverageLogScale (S.threshold j)) := by
  filter_upwards [CounterexampleSequence.eventually_first_threshold_power ha hamax htrack herror S,
    S.threshold_escape.eventually eventually_first_average_window] with j hfirst hwindow
  obtain ⟨μ,hμ,hμu,hcrit,hquarter,_,hfull⟩ := hfirst
  refine ⟨μ,hμ,hμu,hcrit,hquarter,?_⟩
  apply averagedCutPower_lower
  intro t ht
  obtain ⟨hlo,hhi⟩ := hwindow t ht
  have hlower := hfull _ hlo hhi
  have hκ : 0 ≤ S.kappa j := (by norm_num : (0 : ℝ) ≤ 2).trans (S.kappa_ge_two j)
  have hreserve := cutPower_reserve_mono (cappedStep μ (S.threshold j)) (by norm_num : (0 : ℝ) ≤ 1)
    (by norm_num : (0 : ℝ) ≤ 0) hκ (fullCut (Real.exp (firstAverageLogScale (S.threshold j)+t*Real.sqrt (firstAverageLogScale (S.threshold j)))) (S.schedules j))
  exact hlower.trans hreserve

end
end StrongSilver
