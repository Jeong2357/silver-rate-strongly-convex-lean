-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.InitialAveragePower
import StrongSilver.FinalAveragePower
import StrongSilver.CounterexampleLadder

namespace StrongSilver
open Real Filter
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2200000

/-- The total averaged decrease is at least an absolute positive multiple
of W on an actually constructed finite geometric scale ladder. -/
theorem CounterexampleSequence.eventually_averaged_power_drop {a : ℝ} (ha : 0 < a) (hamax : a ≤ 1/128)
    (htrack : 7*initialMarkedLogCoefficient a ≤ 1/2)
    (herror : 2*splitCoefficient*initialStableErrorCoefficient a ≤ powerLogMinimum/16)
    (S : CounterexampleSequence a) : ∀ᶠ j : ℕ in atTop,
    let Y := finalAverageLogScale (weightedCount (S.schedules j) (a*S.kappa j)/((S.schedules j).length : ℝ))
    let U := firstAverageLogScale (S.threshold j)
    ∃ μ : ℝ, ∃ m : ℕ, 1/S.kappa j ≤ μ ∧ μ ≤ 9/(8*S.kappa j) ∧ (∀ b ∈ S.schedules j, 1-μ*b ≠ 0) ∧
      inverseChargeAbove (S.kappa j/4) (S.schedules j) μ ≤ 34*(countAbove (S.schedules j) (S.kappa j/4) : ℝ) ∧
      1 ≤ m ∧ Y ≤ geometricScale U bandRatio m ∧ geometricScale U bandRatio m < bandRatio*Y ∧
      (∀ i ≤ m, Y ≤ geometricScale U bandRatio i ∧ geometricScale U bandRatio i ≤ U) ∧
      (powerLogMinimum/32)*weightedCount (S.schedules j) (a*S.kappa j) ≤
        ∑ i ∈ Finset.range m, averagedPowerDecrease (cappedStep μ (S.threshold j)) (S.kappa j) (S.schedules j)
          (geometricScale U bandRatio i) (geometricScale U bandRatio (i+1)) := by
  have hc : 0 < powerLogMinimum/32 := div_pos powerLogMinimum_positive (by norm_num)
  filter_upwards [CounterexampleSequence.eventually_initial_average_lower ha hamax htrack herror S,
    CounterexampleSequence.eventually_final_average_small ha hamax S hc,S.eventually_geometric_ladder]
    with j hfirst hlast hladder
  dsimp only
  obtain ⟨μ,hμ,hμu,hcrit,hquarter,hinitial⟩ := hfirst
  obtain ⟨m,hm,hYm,hmY,hscales⟩ := hladder
  have hκ : 0 < S.kappa j := lt_of_lt_of_le (by norm_num) (S.kappa_ge_two j)
  have hμ0 : 0 < μ := (one_div_pos.mpr hκ).trans_le hμ
  have hfinal := hlast μ _ hμ0 hμu hYm hmY.le
  refine ⟨μ,m,hμ,hμu,hcrit,hquarter,hm,hYm,hmY,hscales,?_⟩
  rw [averaged_power_telescoping]
  simp only [geometricScale,pow_zero,mul_one]
  dsimp only [geometricScale] at hfinal
  linear_combination hinitial+hfinal

end
end StrongSilver
