-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PowerNormalization

namespace StrongSilver
open Real
noncomputable section
set_option maxHeartbeats 1000000

theorem scalar_slope_budget_power_bound {A K C T b Q e a : ℝ} (hA : 1 ≤ A) (hK : 0 ≤ K)
    (hC0 : 0 ≤ C) (hT0 : 0 < T) (hb0 : 0 < b) (hQ0 : 0 ≤ Q) (he0 : 0 ≤ e)
    (ha : a ≤ C*e) (hC : C ≤ K*A^((3 : ℝ)/1000)) (hT : T ≤ A^((51 : ℝ)/50))
    (hb : A^((499 : ℝ)/500) ≤ b) (he : e^2 = A^(-(3 : ℝ)/25)*T*Q) :
    a*(2*(C/T+1/b)*e) ≤ (2*K^2+2*K)*A^(-(19 : ℝ)/200)*Q := by
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  have hg0 : 0 ≤ 2*(C/T+1/b)*e := mul_nonneg (mul_nonneg (by norm_num)
    (add_nonneg (div_nonneg hC0 hT0.le) (one_div_pos.mpr hb0).le)) he0
  have haG := mul_le_mul_of_nonneg_right ha hg0
  have hTb : T/b ≤ A^((11 : ℝ)/500) := by
    apply (div_le_iff₀ hb0).mpr
    have hm := mul_le_mul_of_nonneg_left hb (Real.rpow_pos_of_pos hA0 ((11 : ℝ)/500)).le
    have hp : A^((11 : ℝ)/500)*A^((499 : ℝ)/500) = A^((51 : ℝ)/50) := by
      rw [← Real.rpow_add hA0]
      congr 1
      norm_num
    rw [hp] at hm
    exact hT.trans hm
  have hCpow : 0 ≤ K*A^((3 : ℝ)/1000) := mul_nonneg hK (Real.rpow_pos_of_pos hA0 _).le
  have hC2 : C^2 ≤ K^2*A^((3 : ℝ)/500) := by
    have hs : C^2 ≤ (K*A^((3 : ℝ)/1000))^2 := by nlinarith only [hC,hC0,hCpow]
    rw [mul_pow,← Real.rpow_mul_natCast hA0.le] at hs
    convert hs using 1 <;> norm_num
  have hCQ := mul_le_mul_of_nonneg_right hC2
    (mul_nonneg (Real.rpow_pos_of_pos hA0 (-(3 : ℝ)/25)).le hQ0)
  have hprod := mul_le_mul hC hTb (div_nonneg hT0.le hb0.le) hCpow
  have hprodQ := mul_le_mul_of_nonneg_right hprod
    (mul_nonneg (Real.rpow_pos_of_pos hA0 (-(3 : ℝ)/25)).le hQ0)
  have hp1 : A^((3 : ℝ)/500)*A^(-(3 : ℝ)/25) = A^(-(57 : ℝ)/500) := by
    rw [← Real.rpow_add hA0]; congr 1; norm_num
  have hp2 : A^((3 : ℝ)/1000)*A^((11 : ℝ)/500)*A^(-(3 : ℝ)/25) = A^(-(19 : ℝ)/200) := by
    rw [power_product_three hA0]; congr 1; norm_num
  have hexp : A^(-(57 : ℝ)/500) ≤ A^(-(19 : ℝ)/200) :=
    Real.rpow_le_rpow_of_exponent_le hA (by norm_num)
  have hsmall := mul_le_mul_of_nonneg_left hexp (sq_nonneg K)
  have hsmallQ := mul_le_mul_of_nonneg_right hsmall hQ0
  have h1 : C^2*A^(-(3 : ℝ)/25)*Q ≤ K^2*A^(-(57 : ℝ)/500)*Q := by
    have hx : (K^2*A^((3 : ℝ)/500))*(A^(-(3 : ℝ)/25)*Q) = K^2*A^(-(57 : ℝ)/500)*Q := by
      rw [← hp1]
      ring
    rw [hx] at hCQ
    nlinarith only [hCQ]
  have h2 : C*(T/b)*A^(-(3 : ℝ)/25)*Q ≤ K*A^(-(19 : ℝ)/200)*Q := by
    have hx : (K*A^((3 : ℝ)/1000)*(A^((11 : ℝ)/500)))*(A^(-(3 : ℝ)/25)*Q) = K*A^(-(19 : ℝ)/200)*Q := by
      rw [← hp2]
      ring
    rw [hx] at hprodQ
    nlinarith only [hprodQ]
  have hsplit : C*e*(2*(C/T+1/b)*e) =
      2*(C^2*A^(-(3 : ℝ)/25)*Q)+2*(C*(T/b)*A^(-(3 : ℝ)/25)*Q) := by
    calc
      _ = (2*C^2/T+2*C/b)*e^2 := by ring
      _ = _ := by rw [he]; field_simp [hT0.ne',hb0.ne'] <;> ring
  rw [hsplit] at haG
  nlinarith only [haG,h1,h2,hsmallQ]

end
end StrongSilver
