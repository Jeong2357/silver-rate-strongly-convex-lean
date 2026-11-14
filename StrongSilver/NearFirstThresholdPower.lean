-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.NearCounterexamplePower

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 1600000

theorem CounterexampleSequence.eventually_near_first_threshold_power {a : ℝ} (ha : 0 < a) (hamax : a ≤ 1/128)
    (htrack : 7*initialMarkedLogCoefficient a ≤ 1/2)
    (herror : 2*splitCoefficient*initialStableErrorCoefficient a ≤ powerLogMinimum/16)
    (S : CounterexampleSequence a) : ∀ᶠ j : ℕ in atTop,
    (S.kappa j)^(1-initialPowerEpsilon) ≤ S.threshold j →
    ∃ μ : ℝ, 1/S.kappa j ≤ μ ∧ μ ≤ 9/(8*S.kappa j) ∧ (∀ b ∈ S.schedules j, 1-μ*b ≠ 0) ∧
      inverseChargeAbove (S.kappa j/4) (S.schedules j) μ ≤ 34*(countAbove (S.schedules j) (S.kappa j/4) : ℝ) ∧
      (powerLogMinimum/16)*weightedCount (S.schedules j) (a*S.kappa j) ≤
        cutPower (cappedStep μ (S.threshold j)) 1 0 (closedCut (S.threshold j) (S.schedules j)) ∧
      ∀ A : ℝ, (S.threshold j)^(1-initialPowerXi) ≤ A → A < S.threshold j →
        (powerLogMinimum/16)*weightedCount (S.schedules j) (a*S.kappa j) ≤
          cutPower (cappedStep μ (S.threshold j)) 1 0 (fullCut A (S.schedules j)) := by
  filter_upwards [CounterexampleSequence.eventually_near_full_cut_power ha hamax htrack herror S,
    S.threshold_escape.eventually (eventually_gt_atTop (1 : ℝ))] with j hbound hB
  intro hnear
  obtain ⟨μ,hμ,hμu,hcrit,hquarter,hfull⟩ := hbound hnear
  have hfloor : (S.threshold j)^(1-initialPowerXi) < S.threshold j := by
    have hh := Real.rpow_lt_rpow_of_exponent_lt hB (show 1-initialPowerXi < 1 by linarith only [initialPowerXi_positive])
    simpa only [Real.rpow_one] using hh
  obtain ⟨A,hA,hAB,he⟩ := exists_fullCut_eq_closedCut (S.schedules j) hfloor
  refine ⟨μ,hμ,hμu,hcrit,hquarter,?_,hfull⟩
  simpa only [he] using hfull A hA hAB

end
end StrongSilver
