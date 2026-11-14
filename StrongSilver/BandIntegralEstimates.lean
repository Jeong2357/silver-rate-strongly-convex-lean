-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandIntegralBudgets

namespace StrongSilver
open Real Filter Set
noncomputable section
set_option maxHeartbeats 3000000

theorem bandExcessConstant_positive : 0 < bandExcessConstant := by
  have hc := split_coefficient_positive
  have hν := nu_positive
  have hd : 0 < 1-nu := by linarith only [nu_lt_one]
  unfold bandExcessConstant bandEndpointConstant bandLogUpperConstant bandPowerUpperConstant
  positivity

theorem bandIntegralConstant_positive : 0 < bandIntegralConstant := by
  have hc := bandExcessConstant_positive
  have hs := split_coefficient_positive
  have hν := nu_positive
  unfold bandIntegralConstant
  positivity

/-- The integrated cut bounds (4.9)--(4.10) for the original stable
signed schedule. Every logarithmic, refinement and endpoint budget is
proved from the source hypotheses, uniformly before choosing the band. -/
theorem eventually_band_integral_estimates : ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ critical : ℝ, ∀ h : List ℝ,
    1 < κ → 1 < B → B ≤ cap → cap ≤ κ → u ≤ firstAverageLogScale B →
    1/κ ≤ μ → μ ≤ 2/κ → μ*B ≤ 1/2 →
    (∀ b ∈ h, 1-μ*b ≠ 0) → inverseChargeAbove (κ/4) h μ ≤ critical →
    critical ≤ 34*weightedCount h cap*cap^(-nu) → D κ h ≤ 1 →
    1 ≤ countAbove h B → κ^nu ≤ weightedCount h cap → BandIntegralBounds κ B cap μ u h := by
  filter_upwards [eventually_band_pointwise_bounds,eventually_outer_band_log_window,
    eventually_outerBand_length,eventually_ge_atTop (1:ℝ)] with u hpoint hwindow hlength hu
  intro κ B cap μ critical h hκ hB hBcap hcapκ hU hμ hμu hμB hcrit hcritical hcriticalRank hD hcount hκW
  have hκ0 := zero_lt_one.trans hκ
  have hμ0 := (one_div_pos.mpr hκ0).trans_le hμ
  apply band_integral_bounds_of_pointwise hκ0.le (zero_lt_one.trans hB).le hμ0
    (show μ*B < 1 by linarith only [hμB]) hu hlength
  · intro y hy
    have W := hwindow B μ y hB hU hμ0 hμB hy
    exact W.2.2.2.2.2.2.2.2.2.2
  · exact hpoint κ B cap μ critical h hκ hB hBcap hcapκ hU hμ hμu hμB hcrit hcritical hcriticalRank hD hcount hκW

end
end StrongSilver
