-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.InnerBandGeometry

namespace StrongSilver
open Real Filter Set
noncomputable section
set_option maxHeartbeats 4300000

theorem eventually_inner_band_kernel_window : ∀ᶠ u : ℝ in atTop,
    ∀ y : ℝ, ∀ k : ℕ, y ∈ Icc (innerBandLow u) (innerBandHigh u) → k ≤ fourPhaseDepth u+2 →
    y ∈ Icc (outerBandLow u) (outerBandHigh u) ∧
      y-(k:ℝ)*Real.log rho ∈ Icc (outerBandLow u) (outerBandHigh u) ∧ y+3*visibilitySpacing ≤ outerBandHigh u := by
  filter_upwards [eventually_inner_band_geometry,eventually_band_depth_sqrt_margin,eventually_band_forest_spacing,
    eventually_ge_atTop (1:ℝ)] with u hGeom hMargin hTol hu
  intro y k hy hk
  have hkr : (k:ℝ) ≤ (fourPhaseDepth u:ℝ)+2 := by exact_mod_cast hk
  have hω := log_rho_positive
  have hδ := hTol.1
  have hRad : 0 ≤ 22*(k:ℝ)*bandTolerance u := by positivity
  have hFact : 0 ≤ Real.log rho+22*bandTolerance u := by positivity
  have hBound := (mul_le_mul_of_nonneg_right hkr hFact).trans hMargin
  have hSpan : (k:ℝ)*Real.log rho ≤ Real.sqrt u := by nlinarith only [hBound,hRad]
  have hkω : 0 ≤ (k:ℝ)*Real.log rho := by positivity
  have hSqrt := Real.sqrt_pos.mpr hGeom.1
  have hLog : 0 ≤ Real.log u/200 := div_nonneg (Real.log_nonneg hu) (by norm_num)
  have hTop : y+3*visibilitySpacing ≤ outerBandHigh u := by
    have hh := hGeom.2.2.2.2.1
    linarith only [hy.2,hh,hLog]
  have hYhi : y ≤ outerBandHigh u := by linarith only [hTop,visibilitySpacing_positive]
  have hLow : outerBandLow u ≤ y-(k:ℝ)*Real.log rho := by
    have hh := hy.1
    dsimp only [innerBandLow] at hh
    dsimp only [outerBandLow]
    linarith only [hh,hSpan,hSqrt]
  exact ⟨⟨hGeom.2.2.2.1.le.trans hy.1,hYhi⟩,⟨hLow,by linarith only [hYhi,hkω]⟩,hTop⟩

end
end StrongSilver
