-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandSourceData

namespace StrongSilver
open Real Filter Set MeasureTheory
noncomputable section
set_option maxHeartbeats 5100000

theorem bandRefinementSavings_nonnegative (κ B μ u y : ℝ) (h : List ℝ) :
    0 ≤ bandRefinementSavings κ B μ u y h := totalGapSavingsMaximum_nonnegative _ _ _ _ _ _

/-- The excluded-gap savings term has the same O(W) budget on any
subinterval, using only the original stable source schedule. -/
theorem eventually_band_refinement_subinterval : ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ critical a b : ℝ, ∀ h : List ℝ,
    BandSourceData κ B cap μ critical u h → a ≤ b → outerBandLow u ≤ a → b ≤ outerBandHigh u →
    (∫ y in a..b, Real.exp (nu*y)*bandRefinementSavings κ B μ u y h) ≤ bandIntegralConstant*weightedCount h cap := by
  filter_upwards [eventually_band_integral_estimates,eventually_band_pointwise_bounds,eventually_gt_atTop (0:ℝ)]
    with u hIntegral hPoint hu
  intro κ B cap μ critical a b h S hab ha hb
  let lo := outerBandLow u
  let hi := outerBandHigh u
  let R := fun y => Real.exp (nu*y)*bandRefinementSavings κ B μ u y h
  let Lp := fun y => Real.exp (nu*y)*bandPositiveLog κ B μ u y h
  let L := fun y => Real.exp (nu*y)*bandSignedLog κ B μ u y h
  have hBounds := hIntegral κ B cap μ critical h S.kappa_gt_one S.threshold_gt_one S.threshold_le_cap S.cap_le_kappa S.scale_upper
    S.curvature_lower S.curvature_upper S.curvature_half S.noncritical S.critical_charge S.critical_rank S.distance_stable S.threshold_count S.rank_lower
  have hCuts := hPoint κ B cap μ critical h S.kappa_gt_one S.threshold_gt_one S.threshold_le_cap S.cap_le_kappa S.scale_upper
    S.curvature_lower S.curvature_upper S.curvature_half S.noncritical S.critical_charge S.critical_rank S.distance_stable S.threshold_count S.rank_lower
  have hRint : IntervalIntegrable R volume lo hi := bandRefinementSavings_weighted_integrable κ B μ u lo hi h
  have hPint : IntervalIntegrable Lp volume lo hi := bandPositiveLog_weighted_integrable κ B μ u lo hi h
  have hLint : IntervalIntegrable L volume lo hi := bandSignedLog_weighted_integrable κ B μ u lo hi h
  have hTotalInt := ((intervalIntegrable_positive_part hPint).add hRint).add (hPint.sub hLint)
  have hDom : ∀ y ∈ Icc lo hi, R y ≤ max (Lp y) 0+R y+(Lp y-L y) := by
    intro y hy
    have hOrder := mul_le_mul_of_nonneg_left (hCuts y hy).log_order (Real.exp_pos (nu*y)).le
    have hMax := le_max_right (Lp y) (0:ℝ)
    dsimp only [Lp,L,R]
    linear_combination hOrder+hMax
  have hFull := intervalIntegral.integral_mono_on (outerBand_order hu.le) hRint hTotalInt hDom
  have hFullBound : (∫ y in lo..hi, R y) ≤ bandIntegralConstant*weightedCount h cap := hFull.trans hBounds.all_gap_upper
  have hNonneg (y : ℝ) : 0 ≤ R y := mul_nonneg (Real.exp_pos _).le (bandRefinementSavings_nonnegative κ B μ u y h)
  have hSub := intervalIntegral.integral_mono_interval ha hab hb (Filter.Eventually.of_forall hNonneg) hRint
  exact hSub.trans hFullBound

end
end StrongSilver
