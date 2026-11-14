-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.Constants

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 2800000

theorem height_positive_mass_normalization {A y : ℝ} (hA : 0 < A) (hupper : A ≤ 2*Real.exp y) :
    Real.exp ((nu-1)*y)*A^(1-nu) ≤ 2 := by
  have hr : 0 < 1-nu := by linarith only [nu_lt_one]
  have hp := Real.rpow_le_rpow hA.le hupper hr.le
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (Real.exp_pos y).le,
    Real.rpow_def_of_pos (Real.exp_pos y),Real.log_exp] at hp
  have htwo : (2:ℝ)^(1-nu) ≤ 2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
      (show 1-nu ≤ (1:ℝ) by linarith only [nu_positive])
  have hh := mul_le_mul_of_nonneg_left hp (Real.exp_pos ((nu-1)*y)).le
  have he : Real.exp ((nu-1)*y)*Real.exp (y*(1-nu)) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  have hEq : Real.exp ((nu-1)*y)*((2:ℝ)^(1-nu)*Real.exp (y*(1-nu))) = (2:ℝ)^(1-nu) := by
    calc
      _ = (2:ℝ)^(1-nu)*(Real.exp ((nu-1)*y)*Real.exp (y*(1-nu))) := by ring
      _ = _ := by rw [he,mul_one]
  exact hh.trans (hEq.le.trans htwo)

end
end StrongSilver
