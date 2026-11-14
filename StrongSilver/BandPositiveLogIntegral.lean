-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandSourceData

namespace StrongSilver
open Real Filter Set MeasureTheory
noncomputable section
set_option maxHeartbeats 3600000

theorem eventually_band_positive_log_subinterval : ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ critical a b : ℝ, ∀ h : List ℝ,
    BandSourceData κ B cap μ critical u h → a ≤ b → outerBandLow u ≤ a → b ≤ outerBandHigh u →
    (∫ y in a..b, max (Real.exp (nu*y)*bandPositiveLog κ B μ u y h) 0) ≤
      (bandExcessConstant/(splitCoefficient*nu))*weightedCount h cap := by
  filter_upwards [eventually_band_integral_estimates] with u H
  intro κ B cap μ critical a b h S hab ha hb
  have hBounds := H κ B cap μ critical h S.kappa_gt_one S.threshold_gt_one S.threshold_le_cap S.cap_le_kappa S.scale_upper
    S.curvature_lower S.curvature_upper S.curvature_half S.noncritical S.critical_charge S.critical_rank S.distance_stable
    S.threshold_count S.rank_lower
  have hInt := intervalIntegrable_positive_part (bandPositiveLog_weighted_integrable κ B μ u (outerBandLow u) (outerBandHigh u) h)
  have hSub := intervalIntegral.integral_mono_interval ha hab hb
    (Filter.Eventually.of_forall (fun y => le_max_right (Real.exp (nu*y)*bandPositiveLog κ B μ u y h) (0:ℝ))) hInt
  have hScale := mul_le_mul_of_nonneg_left hSub (mul_pos split_coefficient_positive nu_positive).le
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (mul_pos split_coefficient_positive nu_positive)).mpr
  linear_combination hScale+hBounds.positive_log_upper

end
end StrongSilver
