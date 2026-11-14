-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FinalAverageWindow
import StrongSilver.AveragedCutPower

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 1800000

/-- The entire last averaging window has negligible actual threshold
power, uniformly for every admissible common curvature. -/
theorem CounterexampleSequence.eventually_final_average_small {a c : ℝ} (ha : 0 < a) (hamax : a ≤ 1/128)
    (S : CounterexampleSequence a) (hc : 0 < c) : ∀ᶠ j : ℕ in atTop,
    ∀ μ v : ℝ, 0 < μ → μ ≤ 9/(8*S.kappa j) →
      finalAverageLogScale (weightedCount (S.schedules j) (a*S.kappa j)/((S.schedules j).length : ℝ)) ≤ v →
      v ≤ bandRatio*finalAverageLogScale (weightedCount (S.schedules j) (a*S.kappa j)/((S.schedules j).length : ℝ)) →
      averagedCutPower (cappedStep μ (S.threshold j)) (S.kappa j) (S.schedules j) v ≤
        c*weightedCount (S.schedules j) (a*S.kappa j) := by
  filter_upwards [CounterexampleSequence.eventually_final_cut_power_small ha hamax S hc,
    S.ratio_escape.eventually eventually_final_average_window,
    S.threshold_escape.eventually (eventually_ge_atTop (1 : ℝ))] with j hpower hwindow hB
  intro μ v hμ hμu hvL hvU
  apply averagedCutPower_upper
  intro t ht
  obtain ⟨hA,hAB,hAmax⟩ := hwindow (S.threshold j) hB (S.ratio_le_threshold_power j) v hvL hvU t ht
  exact hpower μ _ hμ hμu hA hAB hAmax

end
end StrongSilver
