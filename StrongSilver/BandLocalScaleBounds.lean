-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandCandidateUpperScales
import StrongSilver.ComparableRealPowers
import StrongSilver.FourPhaseDepthAsymptotics

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 6200000

def bandLocalLowerDenominator : ℝ := 100000*Real.exp 3
def bandLocalCommonConstant : ℝ := 2*bandLocalLowerDenominator+16
def bandLocalLowerScale (u A : ℝ) : ℝ := A/(bandLocalLowerDenominator*(4:ℝ)^(fourPhaseDepth u+2))

theorem bandLocalLowerDenominator_positive : 0 < bandLocalLowerDenominator := mul_pos (by norm_num) (Real.exp_pos _)
theorem bandLocalCommonConstant_positive : 0 < bandLocalCommonConstant := by
  have hk := bandLocalLowerDenominator_positive
  unfold bandLocalCommonConstant
  positivity

/-- The concrete band scales satisfy the logarithmic common bounds
required by the finite two-gap budget theorem. -/
theorem eventually_band_local_scale_bounds : ∀ᶠ u : ℝ in atTop,
    ∀ A : ℝ, 0 < A → 1 ≤ Real.log A → u ≤ 2*Real.log A → Real.log A ≤ 2*u →
    A/(bandLocalCommonConstant*(Real.log A)^((1:ℝ)/1000)) ≤ bandLocalLowerScale u A ∧
    bandLocalUpperScale u A ≤ bandLocalCommonConstant*A*(Real.log A)^((1:ℝ)/100) ∧
    bandLocalNegativeScale u A ≤ bandLocalCommonConstant*A*(Real.log A)^(-(1:ℝ)/10+(1:ℝ)/100) := by
  filter_upwards [eventually_fourPhaseScaleDenominator_le_power (by norm_num : (0:ℝ) < 1/2000),
    eventually_gt_atTop (0:ℝ)] with u hDepth hu
  intro A hA hLog huLog hLogu
  have hx := zero_lt_one.trans_le hLog
  have hK := bandLocalLowerDenominator_positive
  have hCommon16 : (16:ℝ) ≤ bandLocalCommonConstant := by unfold bandLocalCommonConstant; linarith only [hK]
  have hCommon2K : 2*bandLocalLowerDenominator ≤ bandLocalCommonConstant := by unfold bandLocalCommonConstant; linarith only
  have hScaleD := comparable_rpow_upper hu hx huLog hLogu
    (by norm_num : (-1:ℝ) ≤ 1/2000) (by norm_num : (1:ℝ)/2000 ≤ 1)
  have hScaleU := comparable_rpow_upper hu hx huLog hLogu
    (by norm_num : (-1:ℝ) ≤ 1/200) (by norm_num : (1:ℝ)/200 ≤ 1)
  have hScaleN := comparable_rpow_upper hu hx huLog hLogu
    (by norm_num : (-1:ℝ) ≤ -(19:ℝ)/200) (by norm_num : -(19:ℝ)/200 ≤ 1)
  have hPowerD := Real.rpow_le_rpow_of_exponent_le hLog (by norm_num : (1:ℝ)/2000 ≤ 1/1000)
  have hPowerU := Real.rpow_le_rpow_of_exponent_le hLog (by norm_num : (1:ℝ)/200 ≤ 1/100)
  have hPowerN := Real.rpow_le_rpow_of_exponent_le hLog (by norm_num : -(19:ℝ)/200 ≤ -(1:ℝ)/10+(1:ℝ)/100)
  have hD : (4:ℝ)^(fourPhaseDepth u+2) ≤ 2*(Real.log A)^((1:ℝ)/1000) := by
    linear_combination hDepth+hScaleD+2*hPowerD
  have hDenom : bandLocalLowerDenominator*(4:ℝ)^(fourPhaseDepth u+2) ≤
      bandLocalCommonConstant*(Real.log A)^((1:ℝ)/1000) := by
    have h1 := mul_le_mul_of_nonneg_left hD hK.le
    have h2 := mul_le_mul_of_nonneg_right hCommon2K (Real.rpow_pos_of_pos hx ((1:ℝ)/1000)).le
    linear_combination h1+h2
  have hL : A/(bandLocalCommonConstant*(Real.log A)^((1:ℝ)/1000)) ≤ bandLocalLowerScale u A :=
    div_le_div_of_nonneg_left hA.le (mul_pos hK (pow_pos (by norm_num : (0:ℝ) < 4) _)) hDenom
  have hU : bandLocalUpperScale u A ≤ bandLocalCommonConstant*A*(Real.log A)^((1:ℝ)/100) := by
    have h1 := mul_le_mul_of_nonneg_left hScaleU (show 0 ≤ 4*A by positivity)
    have h2 := mul_le_mul_of_nonneg_left hPowerU (show 0 ≤ 8*A by positivity)
    have h3 := mul_le_mul_of_nonneg_right (show (8:ℝ) ≤ bandLocalCommonConstant by linarith only [hCommon16])
      (mul_nonneg hA.le (Real.rpow_pos_of_pos hx ((1:ℝ)/100)).le)
    unfold bandLocalUpperScale
    linear_combination h1+h2+h3
  have hN : bandLocalNegativeScale u A ≤ bandLocalCommonConstant*A*(Real.log A)^(-(1:ℝ)/10+(1:ℝ)/100) := by
    have h1 := mul_le_mul_of_nonneg_left hScaleN (show 0 ≤ 8*A by positivity)
    have h2 := mul_le_mul_of_nonneg_left hPowerN (show 0 ≤ 16*A by positivity)
    have h3 := mul_le_mul_of_nonneg_right hCommon16
      (mul_nonneg hA.le (Real.rpow_pos_of_pos hx (-(1:ℝ)/10+(1:ℝ)/100)).le)
    unfold bandLocalNegativeScale
    linear_combination h1+h2+h3
  exact ⟨hL,hU,hN⟩

end
end StrongSilver
