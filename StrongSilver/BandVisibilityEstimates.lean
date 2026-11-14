-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandLongVisibility

namespace StrongSilver
open Real Filter Set
noncomputable section
set_option maxHeartbeats 3400000

/-- Uniform visibility on every band of the original stable signed
schedule. All full-cut integral and inverse-cutoff premises are discharged. -/
theorem eventually_band_visibility_estimates : ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ critical s : ℝ, ∀ h : List ℝ,
    1 < κ → 1 < B → B ≤ cap → cap ≤ κ → u ≤ firstAverageLogScale B →
    1/κ ≤ μ → μ ≤ 2/κ → μ*B ≤ 1/2 → 0 ≤ s →
    (∀ b ∈ h, 1-μ*b ≠ 0) → inverseChargeAbove (κ/4) h μ ≤ critical →
    critical ≤ 34*weightedCount h cap*cap^(-nu) → D κ h ≤ 1 →
    1 ≤ countAbove h B → κ^nu ≤ weightedCount h cap →
    visibilityWindowFactor nu s*((bandLongVisibleNodes κ B μ u s h).map fun q =>
      Real.exp (nu*parentedHeight (cappedStep μ B) (bandPad u) q)*
        visibleNodeScore (cappedStep μ B) (bandPad u) (2400/u) (bandEligible μ B u) q.node).sum ≤
      nu*bandIntegralConstant*weightedCount h cap := by
  filter_upwards [eventually_band_integral_estimates,eventually_outer_band_log_window,eventually_ge_atTop (0:ℝ)]
    with u hIntegral hwindow hu
  intro κ B cap μ critical s h hκ hB hBcap hcapκ hU hμ hμu hμB hs hcrit hcritical hcriticalRank hD hcount hκW
  have hκ0 := zero_lt_one.trans hκ
  have hμ0 := (one_div_pos.mpr hκ0).trans_le hμ
  apply band_long_visibility_bound hκ0.le (zero_lt_one.trans hB).le hμ0
    (show μ*B < 1 by linarith only [hμB]) hu hs
  · intro y hy
    exact (hwindow B μ y hB hU hμ0 hμB hy).2.2.2.2.2.2.2.2.2.2
  · exact hIntegral κ B cap μ critical h hκ hB hBcap hcapκ hU hμ hμu hμB hcrit hcritical hcriticalRank hD hcount hκW

end
end StrongSilver
