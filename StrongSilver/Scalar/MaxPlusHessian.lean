-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.Scalar.MaxPlusDiagonal

namespace StrongSilver.Scalar.Silver
open Set
noncomputable section
set_option maxHeartbeats 800000

theorem scalarSecond_at_rho : scalarSecond rho=nu*(2*nu-Real.sqrt 2)/rho^2 := by
  unfold scalarSecond coefficient
  rw [rho_rpow_nu]
  ring

theorem scalarSecond_at_rho_square : scalarSecond (rho^2)=nu*(4*nu-2-Real.sqrt 2)/rho^4 := by
  unfold scalarSecond coefficient
  rw [rho_square_rpow_nu]
  ring

theorem scalarSecond_rho_positive : 0 < scalarSecond rho := by
  rw [scalarSecond_at_rho]
  exact div_pos (mul_pos nu_positive (by linarith [nu_gt_three_quarters,sqrt_two_bounds.2])) (sq_pos_of_pos rho_positive)

theorem symmetric_curvature_formula : scalarSecond rho-2*scalarSecond (rho^2)=
    nu*(nu*(4*Real.sqrt 2-2)-Real.sqrt 2)/rho^4 := by
  rw [scalarSecond_at_rho,scalarSecond_at_rho_square]
  calc
    _ = (nu*(2*nu-Real.sqrt 2)*rho^2-2*nu*(4*nu-2-Real.sqrt 2))/rho^4 := by
      field_simp <;> ring
    _ = _ := by
      congr 1
      unfold rho
      have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
      linear_combination nu*(2*nu-Real.sqrt 2-2)*hs

theorem symmetric_curvature_positive : 0 < scalarSecond rho-2*scalarSecond (rho^2) := by
  rw [symmetric_curvature_formula]
  apply div_pos (mul_pos nu_positive _) (pow_pos rho_positive _)
  have hr := sqrt_two_bounds.1
  have hcoef : 0 < 4*Real.sqrt 2-2 := by linarith
  nlinarith [mul_pos (sub_pos.mpr nu_gt_three_quarters) hcoef]

def hessianMargin : ℝ := min (scalarSecond rho) (scalarSecond rho-2*scalarSecond (rho^2))

theorem hessianMargin_positive : 0 < hessianMargin :=
  lt_min scalarSecond_rho_positive symmetric_curvature_positive

/-- A concrete positive lower bound for the actual Hessian at the minimum. -/
theorem hessian_lower (u v : ℝ) : hessianMargin*(u^2+v^2) ≤
    scalarSecond rho*(u^2+v^2)-scalarSecond (rho^2)*(u+v)^2 := by
  have h1 := mul_le_mul_of_nonneg_right (min_le_left (scalarSecond rho) (scalarSecond rho-2*scalarSecond (rho^2)))
    (sq_nonneg (u-v))
  have h2 := mul_le_mul_of_nonneg_right (min_le_right (scalarSecond rho) (scalarSecond rho-2*scalarSecond (rho^2)))
    (sq_nonneg (u+v))
  unfold hessianMargin
  nlinarith [h1,h2]

theorem scalarSecond_continuousAt (x : ℝ) (hx : 0 < x) : ContinuousAt scalarSecond x := by
  unfold scalarSecond
  have hp : ContinuousAt (fun y : ℝ => y^nu) x :=
    (Real.hasDerivAt_rpow_const (p := nu) (Or.inl hx.ne')).continuousAt
  exact (continuousAt_const.sub (continuousAt_const.mul hp)).div (continuousAt_id.pow 2) (pow_ne_zero _ hx.ne')

/-- Stability of the positive Hessian under explicit coefficient errors. -/
theorem hessian_stability (a b d u v : ℝ)
    (ha : |a-scalarSecond rho| ≤ hessianMargin/6)
    (hb : |b-scalarSecond rho| ≤ hessianMargin/6)
    (hd : |d-scalarSecond (rho^2)| ≤ hessianMargin/6) :
    (hessianMargin/2)*(u^2+v^2) ≤ a*u^2+b*v^2-d*(u+v)^2 := by
  have ha0 := (abs_le.mp ha).1
  have hb0 := (abs_le.mp hb).1
  have hd1 := (abs_le.mp hd).2
  have h1 := mul_le_mul_of_nonneg_right ha0 (sq_nonneg u)
  have h2 := mul_le_mul_of_nonneg_right hb0 (sq_nonneg v)
  have h3 := mul_le_mul_of_nonneg_right hd1 (sq_nonneg (u+v))
  have hm := hessian_lower u v
  have hdiff : (u+v)^2 ≤ 2*(u^2+v^2) := by nlinarith [sq_nonneg (u-v)]
  have h4 := mul_le_mul_of_nonneg_left hdiff (hessianMargin_positive.le)
  nlinarith [h1,h2,h3,hm,h4]

end
end StrongSilver.Scalar.Silver
