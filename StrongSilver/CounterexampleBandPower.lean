-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandPowerDecreaseUpper
import StrongSilver.CounterexampleBandSource
import StrongSilver.GeometricBandRateSum
import StrongSilver.AveragedPowerDrop

namespace StrongSilver
open Real Filter
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 9500000

/-- The actual band upper bounds sum on the very same finite ladder
and curvature used by the averaged power lower bound. -/
theorem CounterexampleSequence.eventually_total_band_power_upper {a : ℝ}
    (ha : 0 < a) (hamax : a ≤ 1/1000000) (S : CounterexampleSequence a) :
    ∃ K > 0, ∀ᶠ j : ℕ in atTop,
    let Y := finalAverageLogScale (weightedCount (S.schedules j) (a*S.kappa j)/((S.schedules j).length:ℝ))
    let U := firstAverageLogScale (S.threshold j)
    ∀ μ : ℝ, 1/S.kappa j ≤ μ → μ ≤ 9/(8*S.kappa j) →
    (∀ b ∈ S.schedules j, 1-μ*b ≠ 0) →
    inverseChargeAbove (S.kappa j/4) (S.schedules j) μ ≤ 34*(countAbove (S.schedules j) (S.kappa j/4):ℝ) →
    ∀ m : ℕ, (∀ i ≤ m, Y ≤ geometricScale U bandRatio i ∧ geometricScale U bandRatio i ≤ U) →
    (∑ i ∈ Finset.range m, averagedPowerDecrease (cappedStep μ (S.threshold j)) (S.kappa j) (S.schedules j)
      (geometricScale U bandRatio i) (geometricScale U bandRatio (i+1))) ≤
      K*weightedCount (S.schedules j) (a*S.kappa j)*
        (1/(2*Real.log bandRatio*(Real.log Y)^2)+Y^(-(1:ℝ)/1000)/(bandRatio^((1:ℝ)/1000)-1)) := by
  obtain ⟨K,hK,HB⟩ := eventually_band_power_decrease_upper
  obtain ⟨u₀,hbounds⟩ := eventually_atTop.mp HB
  have hY := finalAverageLogScale_escape.comp S.ratio_escape
  refine ⟨K,hK,?_⟩
  filter_upwards [S.eventually_uniform_band_source ha hamax,hY.eventually_ge_atTop u₀,hY.eventually_gt_atTop (1:ℝ)]
    with j hSource hYu hY1
  dsimp only
  intro μ hμ hμu hcrit hquarter m hScales
  let Y := finalAverageLogScale (weightedCount (S.schedules j) (a*S.kappa j)/((S.schedules j).length:ℝ))
  let U := firstAverageLogScale (S.threshold j)
  let W := weightedCount (S.schedules j) (a*S.kappa j)
  have hPoint : ∀ i ∈ Finset.range m,
      averagedPowerDecrease (cappedStep μ (S.threshold j)) (S.kappa j) (S.schedules j)
        (geometricScale U bandRatio i) (geometricScale U bandRatio (i+1)) ≤
      K*W*(1/(Real.log (geometricScale U bandRatio i))^3+(geometricScale U bandRatio i)^(-(1:ℝ)/1000)) := by
    intro i hi
    have hiM : i ≤ m := Nat.le_of_lt (Finset.mem_range.mp hi)
    have hSc := hScales i hiM
    have hS := hSource μ hμ hμu hcrit hquarter (geometricScale U bandRatio i) hSc.2
    have hh := hbounds _ (hYu.trans hSc.1) _ _ _ _ _ _ hS
    rw [geometricScale_step]
    exact hh
  have hSum := Finset.sum_le_sum hPoint
  rw [← Finset.mul_sum] at hSum
  have hRate := geometric_band_rate_sum hY1 bandRatio_bounds.1 (by norm_num : (0:ℝ) < 1/1000) m (hScales m le_rfl).1
  have hW := weightedCount_nonneg (S.schedules j) (a*S.kappa j)
  have hScale := mul_le_mul_of_nonneg_left hRate (show 0 ≤ K*W by positivity)
  dsimp only [U,W,Y,Function.comp_def] at hSum hScale ⊢
  norm_num only at hSum hScale ⊢
  exact hSum.trans hScale

end
end StrongSilver
