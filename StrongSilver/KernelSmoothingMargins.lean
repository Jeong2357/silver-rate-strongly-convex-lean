-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseDepthAsymptotics
import StrongSilver.Constants

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 5200000

theorem eventually_kernel_support_margin : ∀ᶠ u : ℝ in atTop,
    ((fourPhaseDepth u:ℝ)+2)*Real.log rho+Real.log 2 ≤ Real.sqrt u := by
  filter_upwards [eventually_fourPhaseDepth_le_power (by norm_num : (0:ℝ) < 1/4),
    eventually_const_mul_power_le (by norm_num : (1:ℝ)/4 < 1/2) (3*Real.log rho+Real.log 2),
    eventually_ge_atTop (1:ℝ)] with u hDepth hPower hu
  have hω := log_rho_positive
  have hLog2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
  have hPow : (1:ℝ) ≤ u^((1:ℝ)/4) := Real.one_le_rpow hu (by norm_num)
  have hD := mul_le_mul_of_nonneg_right hDepth hω.le
  have hConst := mul_le_mul_of_nonneg_left hPow (show 0 ≤ 2*Real.log rho+Real.log 2 by positivity)
  rw [← Real.sqrt_eq_rpow] at hPower
  linear_combination hD+hConst+hPower

theorem eventually_kernel_weight_error_rate : ∀ᶠ u : ℝ in atTop,
    3*((fourPhaseDepth u:ℝ)+2)*Real.log rho/Real.sqrt u ≤ u^(-(1:ℝ)/1000) := by
  filter_upwards [eventually_fourPhaseDepth_le_power (by norm_num : (0:ℝ) < 1/100),
    eventually_const_mul_power_le (by norm_num : -(49:ℝ)/100 < -(1:ℝ)/1000) (9*Real.log rho),
    eventually_ge_atTop (1:ℝ)] with u hDepth hPower hu
  have hu0 := zero_lt_one.trans_le hu
  have hω := log_rho_positive
  have hPow : (1:ℝ) ≤ u^((1:ℝ)/100) := Real.one_le_rpow hu (by norm_num)
  have hD : (fourPhaseDepth u:ℝ)+2 ≤ 3*u^((1:ℝ)/100) := by linarith only [hDepth,hPow]
  have hScale := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hD (show 0 ≤ 3*Real.log rho by positivity)) (Real.sqrt_nonneg u)
  have hEq : 9*Real.log rho*u^((1:ℝ)/100)/Real.sqrt u = 9*Real.log rho*u^(-(49:ℝ)/100) := by
    rw [Real.sqrt_eq_rpow]
    calc
      _ = 9*Real.log rho*(u^((1:ℝ)/100)/u^((1:ℝ)/2)) := by ring
      _ = _ := by rw [← Real.rpow_sub hu0]; norm_num
  calc
    _ ≤ 9*Real.log rho*u^((1:ℝ)/100)/Real.sqrt u := by linear_combination hScale
    _ = _ := hEq
    _ ≤ _ := hPower

end
end StrongSilver
