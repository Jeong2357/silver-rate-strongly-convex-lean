-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ExpQuotientError

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 2000000

theorem discounted_inverse_deviation {μ C : ℝ} (hμ : 0 ≤ μ) (hC : 1/2 ≤ C) :
    |(1-μ)/C-1| ≤ 2*(|C-1|+μ) := by
  have hCp : 0 < C := by linarith only [hC]
  have he : (1-μ)/C-1 = -((C-1)+μ)/C := by field_simp <;> ring
  have habs := abs_add_le (C-1) μ
  rw [abs_of_nonneg hμ] at habs
  have hnon : 0 ≤ |C-1|+μ := add_nonneg (abs_nonneg _) hμ
  rw [he,abs_div,abs_neg,abs_of_pos hCp]
  apply (div_le_iff₀ hCp).mpr
  have hp := mul_le_mul_of_nonneg_right hC hnon
  nlinarith only [habs,hp]

theorem discounted_exp_quotient_error {μ C s : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hC : 1/2 ≤ C) (hs : |μ*s| ≤ 1) :
    |((1-μ)/C)*((Real.exp (μ*s)-1)/μ)-s| ≤
      2*μ*s^2+2*(|C-1|+μ)*|s| := by
  have hCp : 0 < C := by linarith only [hC]
  let w := (1-μ)/C
  let a := (Real.exp (μ*s)-1)/μ
  have hw : 0 ≤ w := div_nonneg (sub_nonneg.mpr hμ1) hCp.le
  have hw2 : w ≤ 2 := by
    have hh : w ≤ C⁻¹ := by
      dsimp [w]
      rw [inv_eq_one_div]
      exact div_le_div_of_nonneg_right (by linarith only [hμ]) hCp.le
    exact hh.trans (inverse_upper_half hC)
  have ha : |a-s| ≤ μ*s^2 := exp_quotient_error hμ hs
  have hwdev : |w-1| ≤ 2*(|C-1|+μ) := discounted_inverse_deviation hμ.le hC
  have he : w*a-s = w*(a-s)+(w-1)*s := by ring
  have hfirst : |w*(a-s)| ≤ 2*μ*s^2 := by
    rw [abs_mul,abs_of_nonneg hw]
    have h1 := mul_le_mul_of_nonneg_left ha hw
    have h2 := mul_le_mul_of_nonneg_right hw2 (mul_nonneg hμ.le (sq_nonneg s))
    nlinarith only [h1,h2]
  have hsecond : |(w-1)*s| ≤ 2*(|C-1|+μ)*|s| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hwdev (abs_nonneg s)
  change |w*a-s| ≤ _
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add hfirst hsecond)

end
end StrongSilver
