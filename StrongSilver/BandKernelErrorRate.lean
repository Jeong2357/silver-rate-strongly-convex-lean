-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandBoundaryWindow
import StrongSilver.PowerMargins
import StrongSilver.BandPadRatio

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 6500000

def bandKernelError (u : ℝ) : ℝ :=
  ((fourPhaseDepth u:ℝ)+2)*bandTolerance u+u*Real.exp (-u/100)+
    u^(-(1:ℝ)/10)*(2:ℝ)^fourPhaseDepth u+u^(-nu/200)

/-- The square of the inverse-linear exponential estimate provides
a summably small bound after multiplying by the band length. -/
theorem eventually_band_exp_length_small : ∀ᶠ u : ℝ in atTop, u*Real.exp (-u/100) ≤ 1/u := by
  filter_upwards [eventually_exp_negative_linear_le_inverse (by norm_num : (0:ℝ) < 1/200),
    eventually_gt_atTop (0:ℝ)] with u hHalf hu
  have hHalf' : Real.exp (-u/200) ≤ 1/u := by convert hHalf using 1 <;> congr 1 <;> ring
  have hSq := (sq_le_sq₀ (Real.exp_pos (-u/200)).le (one_div_nonneg.mpr hu.le)).mpr hHalf'
  have hEq : (Real.exp (-u/200))^2 = Real.exp (-u/100) := by
    rw [pow_two,← Real.exp_add]
    congr 1 <;> ring
  rw [hEq] at hSq
  have hh := mul_le_mul_of_nonneg_left hSq hu.le
  have he : u*(1/u)^2 = 1/u := by field_simp [hu.ne']
  rwa [he] at hh

/-- All explicit normalized kernel errors decay at a fixed positive
power, independently of the source schedule and curvature. -/
theorem eventually_band_kernel_error_rate : ∀ᶠ u : ℝ in atTop, bandKernelError u ≤ 4*u^(-(1:ℝ)/1000) := by
  filter_upwards [eventually_fourPhaseDepth_le_power (by norm_num : (0:ℝ) < 1/100),
    eventually_fourPhaseGroupCount_le_power (by norm_num : (0:ℝ) < 1/100),
    eventually_const_mul_power_le (by norm_num : -(9:ℝ)/100 < -(1:ℝ)/1000) 3,
    eventually_band_exp_length_small,eventually_ge_atTop (1:ℝ)] with u hDepth hCount hPower hExp hu
  have hu0 := zero_lt_one.trans_le hu
  have hδ : 0 ≤ bandTolerance u := (Real.rpow_pos_of_pos hu0 _).le
  have hPow1 : (1:ℝ) ≤ u^((1:ℝ)/100) := Real.one_le_rpow hu (by norm_num)
  have hD : (fourPhaseDepth u:ℝ)+2 ≤ 3*u^((1:ℝ)/100) := by linarith only [hDepth,hPow1]
  have hDs := mul_le_mul_of_nonneg_right hD hδ
  have hProduct : u^((1:ℝ)/100)*bandTolerance u = u^(-(9:ℝ)/100) := by
    unfold bandTolerance
    rw [← Real.rpow_add hu0]
    norm_num
  have hDepthBound : ((fourPhaseDepth u:ℝ)+2)*bandTolerance u ≤ u^(-(1:ℝ)/1000) := by
    calc
      _ ≤ 3*(u^((1:ℝ)/100)*bandTolerance u) := by linear_combination hDs
      _ = 3*u^(-(9:ℝ)/100) := by rw [hProduct]
      _ ≤ _ := hPower
  have hCountScaled := mul_le_mul_of_nonneg_left hCount (Real.rpow_pos_of_pos hu0 (-(1:ℝ)/10)).le
  have hCountProduct : u^(-(1:ℝ)/10)*u^((1:ℝ)/100) = u^(-(9:ℝ)/100) := by rw [← Real.rpow_add hu0]; norm_num
  rw [hCountProduct] at hCountScaled
  have hCountBound := hCountScaled.trans (Real.rpow_le_rpow_of_exponent_le hu (by norm_num : -(9:ℝ)/100 ≤ -(1:ℝ)/1000))
  have hInv : 1/u ≤ u^(-(1:ℝ)/1000) := by
    rw [one_div,← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hu (by norm_num)
  have hLast : u^(-nu/200) ≤ u^(-(1:ℝ)/1000) := Real.rpow_le_rpow_of_exponent_le hu
    (by have hn := nu_gt_three_quarters; linarith only [hn])
  unfold bandKernelError
  linear_combination hDepthBound+hExp+hInv+hCountBound+hLast

end
end StrongSilver
