-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.HeightRankNormalization

namespace StrongSilver
open Real
noncomputable section
set_option maxHeartbeats 2000000

theorem height_power_normalization {A y : ℝ} (hA : 0 < A) (hheight : Real.exp y ≤ 2*A) :
    Real.exp (nu*y)*A^(-nu) ≤ 2 := by
  have heq : Real.exp (nu*y) = (Real.exp y)^nu := by
    rw [Real.rpow_def_of_pos (Real.exp_pos y),Real.log_exp]
    congr 1
    ring
  have hpow := Real.rpow_le_rpow (Real.exp_pos y).le hheight nu_positive.le
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hA.le] at hpow
  have htwo : (2:ℝ)^nu ≤ 2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) nu_lt_one.le
  have hexp : Real.exp (nu*y) ≤ 2*A^nu := by
    rw [heq]
    exact hpow.trans (mul_le_mul_of_nonneg_right htwo (Real.rpow_pos_of_pos hA nu).le)
  have hm := mul_le_mul_of_nonneg_right hexp (Real.rpow_pos_of_pos hA (-nu)).le
  have hcancel : A^nu*A^(-nu) = 1 := by rw [← Real.rpow_add hA,add_neg_cancel,Real.rpow_zero]
  have he : 2*A^nu*A^(-nu) = 2 := by rw [mul_assoc,hcancel,mul_one]
  rwa [he] at hm

end
end StrongSilver
