-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseVectors

namespace StrongSilver.FourPhase
noncomputable section
set_option maxHeartbeats 2600000

def foot0 (x : Shape) : Coordinates := source x-x 0 • slope0 x
def foot1 (x : Shape) : Coordinates := start1 x-x 1 • slope1 x
def foot2 (x : Shape) : Coordinates := start2 x-x 2 • slope2 x
def foot3 (x : Shape) : Coordinates := start3 x-x 3 • slope3 x

variable {x : Shape} (R : Regular x)
include R

theorem a_b1_identity : a x*(1+a x)+b1sq x = bodyScale x/upperTime x := by
  have ha := a_mul_totalTime x R.totalTime_positive.ne'
  unfold b1sq bodyScale
  have hT := R.totalTime_positive.ne'
  have hU := R.upperTime_positive.ne'
  field_simp
  linear_combination upperTime x*(1+a x)*ha

theorem a_b1_b2_identity : a x*(1+a x)+b1sq x+b2sq x = bodyScale x/x 6 := by
  rw [a_b1_identity R]
  unfold b2sq
  ring

theorem foot1_formula : foot1 x = point (upperTime x*a x-q x) (upperTime x*b1 x) 0 0 := by
  have ht := theta_mul_k1 R
  simp only [foot1,start1,start2,start3,slope1,slope2,point_smul,point_add,point_sub]
  unfold upperTime t1
  congr 1 <;> (try ring) <;> linear_combination -b2 x*ht

theorem foot2_formula : foot2 x = point (x 6*a x-q x) (x 6*b1 x) (x 6*b2 x) 0 := by
  simp only [foot2,start2,start3,slope2,point_smul,point_add,point_sub]
  unfold t2
  congr 1 <;> ring

omit R in
theorem foot3_formula : foot3 x = point (-x 7) 0 0 0 := by
  simp only [foot3,start3,slope3,point_smul,point_sub]
  unfold q
  congr 1 <;> ring

omit R in
theorem foot0_eq : foot0 x = foot1 x+x 4 • slope0 x+x 1 • slope1 x := by
  unfold foot0 foot1 source t0
  module

theorem foot1_axis_negative : upperTime x*a x-q x = -a x*leftMass x := by
  have ha := a_mul_totalTime x R.totalTime_positive.ne'
  have hm := totalTime_sub_upperTime x
  linear_combination ha-a x*hm

theorem foot1_common (i : Fin 4) :
    inner ℝ (foot1 x) (![slope0 x,slope1 x,slope2 x,slope3 x] i) = q x-upperTime x*a x := by
  have hb := b1_sq R
  have hi := a_b1_identity R
  have he : upperTime x*(a x*(1+a x)+b1sq x) = bodyScale x := by
    rw [hi]; exact mul_div_cancel₀ _ R.upperTime_positive.ne'
  unfold bodyScale at he
  fin_cases i
  all_goals rw [foot1_formula R]
  all_goals change inner ℝ (point _ _ _ _) (point _ _ _ _) = _
  all_goals rw [point_inner]
  all_goals (try ring)
  all_goals linear_combination he+upperTime x*hb

theorem foot2_tie3 : inner ℝ (foot2 x) (slope2 x-slope3 x) = 0 := by
  rw [foot2_formula R,slope2,slope3,point_sub,point_inner]
  have h := a_b1_b2_identity R
  have hh : x 6*(a x*(1+a x)+b1sq x+b2sq x) = bodyScale x := by
    rw [h]; exact mul_div_cancel₀ _ R.k2_positive.ne'
  unfold bodyScale at hh
  linear_combination hh+x 6*(b1_sq R)+x 6*(b2_sq R)

theorem foot2_above0 : inner ℝ (foot2 x) (slope2 x-slope0 x) = x 6*(1-r2 x)*b2sq x := by
  rw [foot2_formula R,slope2,slope0,point_sub,point_inner]
  linear_combination x 6*(1-r2 x)*(b2_sq R)

theorem foot2_above1 : inner ℝ (foot2 x) (slope2 x-slope1 x) = x 6*(1+theta x)*b2sq x := by
  rw [foot2_formula R,slope2,slope1,point_sub,point_inner]
  linear_combination x 6*(1+theta x)*(b2_sq R)

theorem V_orthogonal_join : inner ℝ (slope0 x-slope1 x) (x 4 • slope0 x+x 1 • slope1 x) = 0 := by
  simp only [slope0,slope1,point_sub,point_smul,point_add,point_inner]
  have hv := v3_sq R
  rw [v3sq_factor] at hv
  have hk : x 4*(x 1/x 4) = x 1 := mul_div_cancel₀ _ R.k0_positive.ne'
  linear_combination x 4*hv+(r2 x+theta x)*(x 4*r2 x-x 1*theta x)*(b2_sq R)+
    theta x*(r2 x+theta x)*b2sq x*hk

end
end StrongSilver.FourPhase
