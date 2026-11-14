-- SPDX-License-Identifier: GPL-3.0-only
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 1600000

/-- A uniform finite remainder estimate for the product-time change. -/
theorem exp_quotient_error {μ s : ℝ} (hμ : 0 < μ) (hs : |μ*s| ≤ 1) :
    |(Real.exp (μ*s)-1)/μ-s| ≤ μ*s^2 := by
  have ht := Real.abs_exp_sub_one_sub_id_le hs
  have he : (Real.exp (μ*s)-1)/μ-s = (Real.exp (μ*s)-1-μ*s)/μ := by field_simp <;> ring
  rw [he,abs_div,abs_of_pos hμ]
  apply (div_le_iff₀ hμ).mpr
  nlinarith only [ht]

theorem inverse_deviation_half {C : ℝ} (hC : 1/2 ≤ C) : |C⁻¹-1| ≤ 2*|C-1| := by
  have hCp : 0 < C := by linarith only [hC]
  have he : C⁻¹-1 = -(C-1)/C := by field_simp <;> ring
  rw [he,abs_div,abs_neg,abs_of_pos hCp]
  apply (div_le_iff₀ hCp).mpr
  have hh := mul_le_mul_of_nonneg_right hC (abs_nonneg (C-1))
  nlinarith only [hh]

theorem inverse_upper_half {C : ℝ} (hC : 1/2 ≤ C) : C⁻¹ ≤ 2 := by
  have hCp : 0 < C := by linarith only [hC]
  rw [inv_eq_one_div]
  exact (div_le_iff₀ hCp).mpr (by linarith only [hC])

end
end StrongSilver
