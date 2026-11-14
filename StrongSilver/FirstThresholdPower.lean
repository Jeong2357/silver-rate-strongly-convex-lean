-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FarFirstThresholdPower
import StrongSilver.NearFirstThresholdPower

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 1800000

/-- The first-threshold power bound on the original schedules, with one
curvature for the closed starting cut and every full cut in the interval. -/
theorem CounterexampleSequence.eventually_first_threshold_power {a : ℝ} (ha : 0 < a) (hamax : a ≤ 1/128)
    (htrack : 7*initialMarkedLogCoefficient a ≤ 1/2)
    (herror : 2*splitCoefficient*initialStableErrorCoefficient a ≤ powerLogMinimum/16)
    (S : CounterexampleSequence a) : ∀ᶠ j : ℕ in atTop,
    ∃ μ : ℝ, 1/S.kappa j ≤ μ ∧ μ ≤ 9/(8*S.kappa j) ∧ (∀ b ∈ S.schedules j, 1-μ*b ≠ 0) ∧
      inverseChargeAbove (S.kappa j/4) (S.schedules j) μ ≤ 34*(countAbove (S.schedules j) (S.kappa j/4) : ℝ) ∧
      (powerLogMinimum/16)*weightedCount (S.schedules j) (a*S.kappa j) ≤
        cutPower (cappedStep μ (S.threshold j)) 1 0 (closedCut (S.threshold j) (S.schedules j)) ∧
      ∀ A : ℝ, (S.threshold j)^(1-initialPowerXi) ≤ A → A < S.threshold j →
        (powerLogMinimum/16)*weightedCount (S.schedules j) (a*S.kappa j) ≤
          cutPower (cappedStep μ (S.threshold j)) 1 0 (fullCut A (S.schedules j)) := by
  filter_upwards [CounterexampleSequence.eventually_far_first_threshold_power ha hamax S,
    CounterexampleSequence.eventually_near_first_threshold_power ha hamax htrack herror S] with j hfar hnear
  by_cases hcase : S.threshold j ≤ (S.kappa j)^(1-initialPowerEpsilon)
  · obtain ⟨μ,hμ,hμu,hcrit,hquarter,hclosed,hfull⟩ := hfar hcase
    have hweaken : (powerLogMinimum/16)*weightedCount (S.schedules j) (a*S.kappa j) ≤
        (powerLogMinimum/8)*weightedCount (S.schedules j) (a*S.kappa j) := by
      have hh := mul_nonneg powerLogMinimum_positive.le (S.weight_positive j).le
      nlinarith only [hh]
    exact ⟨μ,hμ,hμu,hcrit,hquarter,hweaken.trans hclosed,fun A hA hAB => hweaken.trans (hfull A hA hAB)⟩
  · exact hnear (le_of_not_ge hcase)

/-- Absolute parameters for Lemma 3.9 at full cuts, with every analytic
smallness condition and every trajectory construction discharged. -/
theorem exists_absolute_first_threshold_power : ∃ a : ℝ, 0 < a ∧ a ≤ 1/128 ∧
    ∀ S : CounterexampleSequence a, ∀ᶠ j : ℕ in atTop,
      ∃ μ : ℝ, 1/S.kappa j ≤ μ ∧ μ ≤ 9/(8*S.kappa j) ∧ (∀ b ∈ S.schedules j, 1-μ*b ≠ 0) ∧
      inverseChargeAbove (S.kappa j/4) (S.schedules j) μ ≤ 34*(countAbove (S.schedules j) (S.kappa j/4) : ℝ) ∧
        (powerLogMinimum/16)*weightedCount (S.schedules j) (a*S.kappa j) ≤
          cutPower (cappedStep μ (S.threshold j)) 1 0 (closedCut (S.threshold j) (S.schedules j)) ∧
        ∀ A : ℝ, (S.threshold j)^(1-initialPowerXi) ≤ A → A < S.threshold j →
          (powerLogMinimum/16)*weightedCount (S.schedules j) (a*S.kappa j) ≤
            cutPower (cappedStep μ (S.threshold j)) 1 0 (fullCut A (S.schedules j)) := by
  obtain ⟨a,ha,hamax,htrack,herror⟩ := exists_small_initial_cap
  exact ⟨a,ha,hamax,fun S => CounterexampleSequence.eventually_first_threshold_power ha hamax htrack herror S⟩

end
end StrongSilver
