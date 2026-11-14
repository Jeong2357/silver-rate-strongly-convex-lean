-- SPDX-License-Identifier: GPL-3.0-only
-- Elementary silver identities adapted from SilverAudit/SilverConstants.lean,
-- Yechan Jeong and Youngjoon Hong, v1.0.0.
import StrongSilver.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace StrongSilver
noncomputable section

def splitCoefficient : ℝ := nu * (2 - Real.sqrt 2)

theorem nu_eq_log_ratio : nu = Real.log 2 / Real.log rho := by
  unfold nu p
  rw [one_div, inv_div]

theorem sqrt_two_bounds : 1 < Real.sqrt 2 ∧ Real.sqrt 2 < 3/2 := by
  have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn := Real.sqrt_nonneg (2 : ℝ)
  constructor <;> nlinarith

theorem rho_bounds : 2 < rho ∧ rho < 3 := by
  have h := sqrt_two_bounds
  unfold rho
  constructor <;> linarith [h.1,h.2]

theorem rho_positive : 0 < rho := lt_trans (by norm_num) rho_bounds.1

theorem rho_square : rho^2 = 2*rho+1 := by
  have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  unfold rho
  nlinarith

theorem rho_cube : rho^3 = 7+5*Real.sqrt 2 := by
  unfold rho
  have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  linear_combination (Real.sqrt 2+3)*h

theorem log_rho_positive : 0 < Real.log rho := Real.log_pos (by linarith [rho_bounds.1])
theorem log_two_positive : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)

theorem p_positive : 0 < p := div_pos log_rho_positive log_two_positive

theorem nu_positive : 0 < nu := by
  rw [nu_eq_log_ratio]
  exact div_pos log_two_positive log_rho_positive

theorem nu_lt_one : nu < 1 := by
  rw [nu_eq_log_ratio]
  apply (div_lt_one log_rho_positive).mpr
  exact Real.log_lt_log (by norm_num) rho_bounds.1

theorem nu_gt_three_quarters : 3/4 < nu := by
  have hlt : rho^3 < 16 := by rw [rho_cube]; linarith [sqrt_two_bounds.2]
  have hlog := Real.log_lt_log (pow_pos rho_positive 3) hlt
  have h16 : (16 : ℝ) = 2^4 := by norm_num
  rw [h16, Real.log_pow, Real.log_pow] at hlog
  rw [nu_eq_log_ratio]
  apply (lt_div_iff₀ log_rho_positive).mpr
  norm_num at hlog
  linarith

theorem nu_lt_four_fifths : nu < 4/5 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hspos := Real.sqrt_nonneg (2 : ℝ)
  have hslow : (5 : ℝ)/4 < Real.sqrt 2 := by nlinarith
  have h4 : rho^4 = 17+12*Real.sqrt 2 := by
    unfold rho
    linear_combination (Real.sqrt 2 ^ 2 + 4 * Real.sqrt 2 + 8) * hs
  have hlt : (32 : ℝ) < rho^4 := by rw [h4]; linarith
  have hlog := Real.log_lt_log (by norm_num : (0 : ℝ) < 32) hlt
  have h32 : (32 : ℝ) = 2^5 := by norm_num
  rw [h32, Real.log_pow, Real.log_pow] at hlog
  rw [nu_eq_log_ratio]
  apply (div_lt_iff₀ log_rho_positive).mpr
  norm_num at hlog
  linarith

theorem rho_rpow_nu : rho^nu = 2 := by
  rw [Real.rpow_def_of_pos rho_positive]
  have he : Real.log rho*nu = Real.log 2 := by
    rw [nu_eq_log_ratio]
    field_simp [log_rho_positive.ne']
  rw [he, Real.exp_log (by norm_num : (0 : ℝ) < 2)]

theorem rho_square_rpow_nu : (rho^2)^nu = 4 := by
  rw [← Real.rpow_pow_comm rho_positive.le, rho_rpow_nu]
  norm_num

theorem split_coefficient_positive : 0 < splitCoefficient := by
  apply mul_pos nu_positive
  linarith [sqrt_two_bounds.2]

end
end StrongSilver
