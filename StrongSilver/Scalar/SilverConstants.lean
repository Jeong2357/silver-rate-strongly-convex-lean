-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.Scalar.Problem
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

namespace StrongSilver.Scalar.Silver
noncomputable section
set_option maxHeartbeats 800000

def rho : ℝ := 1+Real.sqrt 2
def nu : ℝ := Real.log 2/Real.log rho
def coefficient : ℝ := nu*(2-Real.sqrt 2)
def minimum : ℝ := (2-Real.sqrt 2)*(1-Real.log (2-Real.sqrt 2))

theorem sqrt_two_bounds : 1 < Real.sqrt 2 ∧ Real.sqrt 2 < 3/2 := by
  have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn := Real.sqrt_nonneg (2 : ℝ)
  constructor <;> nlinarith

theorem rho_bounds : 2 < rho ∧ rho < 3 := by
  have h := sqrt_two_bounds
  unfold rho
  constructor <;> linarith [h.1,h.2]

theorem rho_positive : 0 < rho := lt_trans (by norm_num) rho_bounds.1

theorem rho_square : rho^2=2*rho+1 := by
  have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  unfold rho
  nlinarith

theorem rho_cube : rho^3=7+5*Real.sqrt 2 := by
  unfold rho
  have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  linear_combination (Real.sqrt 2+3)*h

theorem rho_cube_lt_sixteen : rho^3 < 16 := by rw [rho_cube]; linarith [sqrt_two_bounds.2]

theorem log_rho_positive : 0 < Real.log rho := Real.log_pos (by linarith [rho_bounds.1])
theorem log_two_positive : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)

theorem nu_positive : 0 < nu := div_pos log_two_positive log_rho_positive

theorem nu_lt_one : nu < 1 := by
  apply (div_lt_one log_rho_positive).mpr
  exact Real.log_lt_log (by norm_num) rho_bounds.1

theorem nu_gt_three_quarters : 3/4 < nu := by
  have hlog : Real.log (rho^3) < Real.log (16 : ℝ) :=
    Real.log_lt_log (pow_pos rho_positive _) rho_cube_lt_sixteen
  have h16 : (16 : ℝ)=2^4 := by norm_num
  rw [h16,Real.log_pow,Real.log_pow] at hlog
  apply (lt_div_iff₀ log_rho_positive).mpr
  norm_num at hlog
  linarith

theorem nu_is_inverse_exponent : nu=Problem.silverExponent⁻¹ := by
  unfold nu Problem.silverExponent rho
  rw [inv_div]

theorem rho_rpow_nu : rho^nu=2 := by
  rw [Real.rpow_def_of_pos rho_positive]
  have he : Real.log rho*nu=Real.log 2 := by unfold nu; field_simp [log_rho_positive.ne']
  rw [he,Real.exp_log (by norm_num : (0 : ℝ) < 2)]

theorem rho_square_rpow_nu : (rho^2)^nu=4 := by
  rw [← Real.rpow_pow_comm rho_positive.le,rho_rpow_nu]
  norm_num

theorem inverse_rho_rpow_nu : (rho⁻¹)^nu=1/2 := by rw [Real.inv_rpow rho_positive.le,rho_rpow_nu]; norm_num

theorem coefficient_positive : 0 < coefficient := by
  apply mul_pos nu_positive
  linarith [sqrt_two_bounds.2]

theorem minimum_positive : 0 < minimum := by
  have h0 : 0 < 2-Real.sqrt 2 := by linarith [sqrt_two_bounds.2]
  have h1 : 2-Real.sqrt 2 < 1 := by linarith [sqrt_two_bounds.1]
  have hl : Real.log (2-Real.sqrt 2) < 0 := Real.log_neg h0 h1
  exact mul_pos h0 (by linarith)

end
end StrongSilver.Scalar.Silver
