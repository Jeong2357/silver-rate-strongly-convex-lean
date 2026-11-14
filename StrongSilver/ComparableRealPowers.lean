-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.Constants

namespace StrongSilver
open Real
noncomputable section
set_option maxHeartbeats 3600000

/-- Factor-two comparable positive scales remain comparable under
any exponent between minus one and one. -/
theorem comparable_rpow_upper {a b r : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a ≤ 2*b) (hba : b ≤ 2*a) (hrlo : -1 ≤ r) (hrhi : r ≤ 1) : a^r ≤ 2*b^r := by
  by_cases hr : 0 ≤ r
  · have hh := Real.rpow_le_rpow ha.le hab hr
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hb.le] at hh
    have hTwo : (2:ℝ)^r ≤ 2 := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hrhi
    exact hh.trans (mul_le_mul_of_nonneg_right hTwo (Real.rpow_pos_of_pos hb r).le)
  · have hnonpos : r ≤ 0 := (lt_of_not_ge hr).le
    have hLow : b/2 ≤ a := by linarith only [hba]
    have hh := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < b/2) hLow hnonpos
    rw [Real.div_rpow hb.le (by norm_num : (0:ℝ) ≤ 2),div_eq_mul_inv,← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)] at hh
    have hTwo : (2:ℝ)^(-r) ≤ 2 := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
        (show -r ≤ (1:ℝ) by linarith only [hrlo])
    have hScale := mul_le_mul_of_nonneg_left hTwo (Real.rpow_pos_of_pos hb r).le
    exact hh.trans (hScale.trans_eq (by ring))

end
end StrongSilver
