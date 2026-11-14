-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ScalarPaddingPower

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 1400000

theorem scalar_padding_linear_power_bound {A K C T Q e a : ℝ} (hA : 0 < A) (hK : 0 ≤ K)
    (hC0 : 0 ≤ C) (he0 : 0 ≤ e) (ha0 : 0 ≤ a) (ha : a ≤ C*e)
    (hC : C ≤ K*A^((3 : ℝ)/1000)) (hT : T ≤ A^((51 : ℝ)/50))
    (hQ0 : 0 ≤ Q) (he : e^2 = A^(-(3 : ℝ)/25)*T*Q) :
    a^2 ≤ K^2*A^((453 : ℝ)/500)*Q := by
  have hsq : a^2 ≤ (C*e)^2 := by nlinarith only [ha,ha0,mul_nonneg hC0 he0]
  have hKpow : 0 ≤ K*A^((3 : ℝ)/1000) := mul_nonneg hK (Real.rpow_pos_of_pos hA _).le
  have hCsq : C^2 ≤ (K*A^((3 : ℝ)/1000))^2 := by nlinarith only [hC,hC0,hKpow]
  have hCsq' : C^2 ≤ K^2*A^((3 : ℝ)/500) := by
    rw [mul_pow,← Real.rpow_mul_natCast hA.le] at hCsq
    convert hCsq using 1 <;> norm_num
  have h1 := mul_le_mul_of_nonneg_right hCsq' (sq_nonneg e)
  have heT := mul_le_mul_of_nonneg_left hT (Real.rpow_pos_of_pos hA (-(3 : ℝ)/25)).le
  have h2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right heT hQ0)
    (mul_nonneg (sq_nonneg K) (Real.rpow_pos_of_pos hA ((3 : ℝ)/500)).le)
  have hpower : A^((3 : ℝ)/500)*A^(-(3 : ℝ)/25)*A^((51 : ℝ)/50) = A^((453 : ℝ)/500) := by
    rw [power_product_three hA]; congr 1; norm_num
  have heq : (K^2*A^((3 : ℝ)/500))*(A^(-(3 : ℝ)/25)*A^((51 : ℝ)/50)*Q) = K^2*A^((453 : ℝ)/500)*Q := by
    rw [← hpower]; ring
  rw [heq] at h2
  rw [mul_pow] at hsq
  rw [he] at h1 hsq
  nlinarith only [hsq,h1,h2]

end
end StrongSilver
