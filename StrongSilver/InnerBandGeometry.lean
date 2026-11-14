-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandBoundaryWindow
import StrongSilver.BandBinGeometry

namespace StrongSilver
open Real Filter Set
noncomputable section
set_option maxHeartbeats 5800000

def innerBandLow (u : ℝ) : ℝ := u/bandRatio-Real.sqrt u
def innerBandHigh (u : ℝ) : ℝ := u+2*Real.sqrt u

/-- The logarithmic grouping depth and all its boundary tolerances
fit within one square-root margin of the actual paper band. -/
theorem eventually_band_depth_sqrt_margin : ∀ᶠ u : ℝ in atTop,
    ((fourPhaseDepth u:ℝ)+2)*(Real.log rho+22*bandTolerance u) ≤ Real.sqrt u := by
  filter_upwards [eventually_fourPhaseDepth_le_power (by norm_num : (0:ℝ) < 1/4),
    eventually_band_forest_spacing,eventually_const_mul_power_le (by norm_num : (1:ℝ)/4 < 1/2) (3*(Real.log rho+22)),
    eventually_ge_atTop (1:ℝ)] with u hDepth hTol hPower hu
  have hω := log_rho_positive
  have hδ1 : bandTolerance u ≤ 1 := hTol.2.1.trans (by norm_num)
  have hPow : (1:ℝ) ≤ u^((1:ℝ)/4) := Real.one_le_rpow hu (by norm_num)
  have hD : (fourPhaseDepth u:ℝ)+2 ≤ 3*u^((1:ℝ)/4) := by linarith only [hDepth,hPow]
  have hS : Real.log rho+22*bandTolerance u ≤ Real.log rho+22 := by linarith only [hδ1]
  have hMul := mul_le_mul hD hS (by have hh := hTol.1; positivity) (by positivity : 0 ≤ 3*u^((1:ℝ)/4))
  rw [← Real.sqrt_eq_rpow] at hPower
  linear_combination hMul+hPower

/-- Window endpoints and boundary strips lie strictly inside the
protected original band; the availability margin is also satisfied. -/
theorem eventually_inner_band_geometry : ∀ᶠ u : ℝ in atTop,
    0 < u ∧ 1 ≤ fourPhaseDepth u ∧ innerBandLow u ≤ innerBandHigh u ∧
    outerBandLow u < innerBandLow u ∧
    innerBandHigh u+Real.log u/200+3*visibilitySpacing ≤ outerBandHigh u ∧
    ∀ y z : ℝ, ∀ k : ℕ, y ∈ Icc (innerBandLow u) (innerBandHigh u) → k ≤ fourPhaseDepth u+2 →
      |y-z-(k:ℝ)*Real.log rho| ≤ 22*(k:ℝ)*bandTolerance u →
      outerBandLow u < z ∧ z+3*visibilitySpacing ≤ outerBandHigh u := by
  have hLog := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (2:ℝ))
  filter_upwards [eventually_band_depth_sqrt_margin,eventually_band_forest_spacing,hLog,
    eventually_const_mul_log_pow_le_power 1 (1:ℝ) (by norm_num : (0:ℝ) < 1/2),
    eventually_ge_atTop ((3*visibilitySpacing)^2+1),eventually_gt_atTop (0:ℝ)]
    with u hMargin hTol hLog hLogSqrt hLarge hu
  have hSpacing := visibilitySpacing_positive
  have hSqrt := Real.sqrt_pos.mpr hu
  have hSqrtSpacing : 3*visibilitySpacing ≤ Real.sqrt u := by
    apply (Real.le_sqrt (by positivity : 0 ≤ 3*visibilitySpacing) hu.le).mpr
    linarith only [hLarge]
  have hLogSqrt' : Real.log u ≤ Real.sqrt u := by simpa only [pow_one,one_mul,← Real.sqrt_eq_rpow] using hLogSqrt
  have hDepth : 1 ≤ fourPhaseDepth u := by
    have hh := (fourPhaseDepth_group_count_bounds (by linarith only [hLog])).1
    by_contra hn
    have hz : fourPhaseDepth u = 0 := by omega
    rw [hz,pow_zero] at hh
    have hCube : (2:ℝ)^3 ≤ (Real.log u)^3 := by gcongr
    norm_num at hCube
    linarith only [hh,hCube]
  have hRatio := zero_lt_one.trans bandRatio_bounds.1
  have hDiv : u/bandRatio ≤ u := by
    apply (div_le_iff₀ hRatio).mpr
    have hh := mul_le_mul_of_nonneg_right bandRatio_bounds.1.le hu.le
    nlinarith only [hh]
  refine ⟨hu,hDepth,?_,?_,?_,?_⟩
  · dsimp only [innerBandLow,innerBandHigh]
    linarith only [hDiv,hSqrt]
  · dsimp only [outerBandLow,innerBandLow]
    linarith only [hSqrt]
  · dsimp only [innerBandHigh,outerBandHigh]
    linarith only [hLogSqrt',hSqrtSpacing,hSqrt]
  · intro y z k hy hk hStrip
    have hkr : (k:ℝ) ≤ (fourPhaseDepth u:ℝ)+2 := by exact_mod_cast hk
    have hFactor : 0 ≤ Real.log rho+22*bandTolerance u := by have hω := log_rho_positive; have hδ := hTol.1; positivity
    have hBound := (mul_le_mul_of_nonneg_right hkr hFactor).trans hMargin
    have hω := log_rho_positive
    have hLo := (abs_le.mp hStrip).1
    have hHi := (abs_le.mp hStrip).2
    have hkω : 0 ≤ (k:ℝ)*Real.log rho := by positivity
    have hRad : 22*(k:ℝ)*bandTolerance u ≤ Real.sqrt u := by nlinarith only [hBound,hkω]
    dsimp only [innerBandLow,innerBandHigh] at hy
    dsimp only [outerBandLow,outerBandHigh]
    constructor
    · nlinarith only [hy.1,hLo,hHi,hBound,hSqrt]
    · nlinarith only [hy.2,hLo,hkω,hRad,hSqrtSpacing]

end
end StrongSilver
