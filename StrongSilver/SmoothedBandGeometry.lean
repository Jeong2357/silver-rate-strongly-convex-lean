-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.SmoothedBandWeight
import StrongSilver.BandLogWindow

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 5600000

theorem band_lower_scale_positive {u : ℝ} (hu : 0 < u) : 0 < u/bandRatio := div_pos hu (zero_lt_one.trans bandRatio_bounds.1)

/-- The two smoothing windows at u and u/r are separated for large u. -/
theorem eventually_band_smoothing_separated : ∀ᶠ u : ℝ in atTop,
    0 < u ∧ u/bandRatio+Real.sqrt (u/bandRatio) ≤ u := by
  have hr := zero_lt_one.trans bandRatio_bounds.1
  have hc : 0 < 1-1/bandRatio := by
    have hh : 1/bandRatio < 1 := (div_lt_iff₀ hr).mpr (by linarith only [bandRatio_bounds.1])
    linarith only [hh]
  filter_upwards [eventually_sqrt_affine_le_linear hc 1 0,eventually_gt_atTop (0:ℝ)] with u hSmall hu
  have hDiv : u/bandRatio ≤ u := (div_le_iff₀ hr).mpr (by
    have hh := mul_le_mul_of_nonneg_left bandRatio_bounds.1.le hu.le
    linarith only [hh])
  have hSqrt := Real.sqrt_le_sqrt hDiv
  refine ⟨hu,?_⟩
  linear_combination hSmall+hSqrt

/-- A uniform logarithmic-threshold Lipschitz constant for the actual
adjacent geometric smoothing windows. -/
theorem band_weight_lipschitz {u : ℝ} (hu : 0 < u) (x y : ℝ) :
    |smoothedBandWeight u (u/bandRatio) x-smoothedBandWeight u (u/bandRatio) y| ≤
      (3/Real.sqrt u)*|x-y| := by
  have hr := zero_lt_one.trans bandRatio_bounds.1
  have hv := band_lower_scale_positive hu
  have hRatio : bandRatio ≤ 4 := bandRatio_bounds.2.le.trans (by norm_num)
  have hLow : u/4 ≤ u/bandRatio := div_le_div_of_nonneg_left hu.le hr hRatio
  have hSqrt := Real.sqrt_le_sqrt hLow
  rw [Real.sqrt_div hu.le] at hSqrt
  norm_num at hSqrt
  have hRoot := Real.sqrt_pos.mpr hu
  have hRootV := Real.sqrt_pos.mpr hv
  have hInv : 1/Real.sqrt (u/bandRatio) ≤ 2/Real.sqrt u :=
    (div_le_div_iff₀ hRootV hRoot).mpr (by linarith only [hSqrt])
  have hFactor : 1/Real.sqrt u+1/Real.sqrt (u/bandRatio) ≤ 3/Real.sqrt u := by linear_combination hInv
  have hScale := mul_le_mul_of_nonneg_right hFactor (abs_nonneg (x-y))
  exact (smoothedBandWeight_lipschitz hu hv x y).trans hScale

end
end StrongSilver
