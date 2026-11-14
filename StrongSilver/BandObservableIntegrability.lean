-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandCutObservables
import StrongSilver.IntegratedGapBudget

namespace StrongSilver
open Real Filter MeasureTheory
noncomputable section
set_option maxHeartbeats 2600000

theorem continuous_bandCutoff (μ u : ℝ) : Continuous (bandCutoff μ u) := by
  unfold bandCutoff logarithmicCutoff
  fun_prop

theorem bandSignedLog_weighted_integrable (κ B μ u a b : ℝ) (h : List ℝ) :
    IntervalIntegrable (fun y => Real.exp (nu*y)*bandSignedLog κ B μ u y h) volume a b := by
  exact weighted_cutObservable_intervalIntegrable
    (fun C => cutLogProduct (cappedStep μ B) (bandPad u) κ C-Real.log κ) 0 h
    (bandCutoff μ u) (fun y => Real.exp (nu*y)) (continuous_bandCutoff μ u).measurable
    (by fun_prop) a b

theorem bandPositiveLog_weighted_integrable (κ B μ u a b : ℝ) (h : List ℝ) :
    IntervalIntegrable (fun y => Real.exp (nu*y)*bandPositiveLog κ B μ u y h) volume a b := by
  exact weighted_cutObservable_intervalIntegrable
    (fun C => cutLogProduct (positivePartStep (cappedStep μ B)) (bandPad u) κ C-Real.log κ) 0 h
    (bandCutoff μ u) (fun y => Real.exp (nu*y)) (continuous_bandCutoff μ u).measurable
    (by fun_prop) a b

theorem bandRefinementSavings_weighted_integrable (κ B μ u a b : ℝ) (h : List ℝ) :
    IntervalIntegrable (fun y => Real.exp (nu*y)*bandRefinementSavings κ B μ u y h) volume a b := by
  exact weighted_cutObservable_intervalIntegrable
    (totalGapSavingsMaximum (cappedStep μ B) (bandPad u) κ (2400/u) (bandEligible μ B u)) 0 h
    (bandCutoff μ u) (fun y => Real.exp (nu*y)) (continuous_bandCutoff μ u).measurable
    (by fun_prop) a b

theorem outerBand_order {u : ℝ} (hu : 0 ≤ u) : outerBandLow u ≤ outerBandHigh u := by
  have hr := zero_lt_one.trans bandRatio_bounds.1
  have hdiv : u/bandRatio ≤ u := by
    apply (div_le_iff₀ hr).mpr
    have hh := mul_le_mul_of_nonneg_left bandRatio_bounds.1.le hu
    simpa only [mul_one] using hh
  unfold outerBandLow outerBandHigh
  have hs := Real.sqrt_nonneg u
  linarith only [hdiv,hs]

theorem eventually_outerBand_length : ∀ᶠ u : ℝ in atTop, outerBandHigh u-outerBandLow u ≤ 2*u := by
  filter_upwards [eventually_ge_atTop (0:ℝ),
    eventually_sqrt_affine_le_linear zero_lt_one 7 0] with u hu hh
  have hr := zero_lt_one.trans bandRatio_bounds.1
  have hd := div_nonneg hu hr.le
  unfold outerBandLow outerBandHigh
  linarith only [hh,hd]

end
end StrongSilver
