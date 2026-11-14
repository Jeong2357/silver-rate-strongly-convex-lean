-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseVectors

namespace StrongSilver.FourPhase
noncomputable section
set_option maxHeartbeats 2600000

variable {x : Shape} (R : Regular x)
include R

theorem slope01_difference : inner ℝ (slope0 x) (slope0 x-slope1 x) =
    (x 1/x 4)*theta x*(r2 x+theta x)*b2sq x := by
  simp only [slope0,slope1,point_sub,point_inner]
  have hb := b2_sq R
  have hv := v3_sq R
  rw [v3sq_factor] at hv
  linear_combination hv+r2 x*(r2 x+theta x)*hb

theorem slope10_difference : inner ℝ (slope1 x) (slope1 x-slope0 x) =
    theta x*(theta x+r2 x)*b2sq x := by
  simp only [slope0,slope1,point_sub,point_inner]
  linear_combination theta x*(theta x+r2 x)*(b2_sq R)

theorem slope12_difference : inner ℝ (slope1 x) (slope1 x-slope2 x) =
    theta x*(theta x+1)*b2sq x := by
  simp only [slope1,slope2,point_sub,point_inner]
  linear_combination theta x*(theta x+1)*(b2_sq R)

theorem slope21_difference : inner ℝ (slope2 x) (slope2 x-slope1 x) =
    (1+theta x)*b2sq x := by
  simp only [slope1,slope2,point_sub,point_inner]
  linear_combination (1+theta x)*(b2_sq R)

theorem slope20_difference : inner ℝ (slope2 x) (slope2 x-slope0 x) =
    (1-r2 x)*b2sq x := by
  simp only [slope0,slope2,point_sub,point_inner]
  linear_combination (1-r2 x)*(b2_sq R)

theorem slope02_difference : inner ℝ (slope0 x) (slope0 x-slope2 x) =
    ((x 1/x 4)*theta x*(r2 x+theta x)-r2 x*(1+theta x))*b2sq x := by
  simp only [slope0,slope2,point_sub,point_inner]
  have hv := v3_sq R
  rw [v3sq_factor] at hv
  linear_combination hv+r2 x*(r2 x-1)*(b2_sq R)

def slope (x : Shape) : Fin 4 → Coordinates := ![slope0 x,slope1 x,slope2 x,slope3 x]

omit R in
@[simp] theorem slope_zero : slope x 0 = slope0 x := rfl
omit R in
@[simp] theorem slope_one : slope x 1 = slope1 x := rfl
omit R in
@[simp] theorem slope_two : slope x 2 = slope2 x := rfl
omit R in
@[simp] theorem slope_three : slope x 3 = slope3 x := rfl

omit R in
theorem slope_axis (i : Fin 3) : inner ℝ (slope x i.castSucc) axis = a x := by
  fin_cases i <;> exact point_inner_axis _ _ _ _

theorem slope_self_difference_nonnegative (i j : Fin 4) :
    0 ≤ inner ℝ (slope x i) (slope x i-slope x j) := by
  have ht : 0 < theta x := zero_lt_one.trans R.theta_gt_one
  have hr := R.r2_positive
  have hb := R.b2sq_positive
  have ha := R.a_positive
  have hratio : 1 < x 1/x 4 := (one_lt_div R.k0_positive).mpr R.m1_gt_k0
  have h02 : 0 < (x 1/x 4)*theta x*(r2 x+theta x)-r2 x*(1+theta x) := by
    have hp : 0 < theta x*(r2 x+theta x) := mul_pos ht (add_pos hr ht)
    have hmul := mul_lt_mul_of_pos_right hratio hp
    have hth : 1 < theta x^2 := by nlinarith only [R.theta_gt_one]
    nlinarith only [hmul,hth,R.r2_lt_one]
  fin_cases i <;> fin_cases j
  all_goals simp only [slope,Matrix.cons_val_zero',Matrix.cons_val_succ']
  all_goals first
    | simp only [sub_self,inner_zero_right,le_refl]
    | (rw [slope01_difference R]; positivity)
    | (rw [slope10_difference R]; positivity)
    | (rw [slope12_difference R]; positivity)
    | (rw [slope21_difference R]; positivity)
    | (rw [slope20_difference R]; exact mul_nonneg (sub_nonneg.mpr R.r2_lt_one.le) hb.le)
    | (rw [slope02_difference R]; exact (mul_pos h02 hb).le)
    | (simp only [slope0,slope1,slope2,slope3,point_sub,point_inner]; nlinarith [sq_nonneg (a x),sq_nonneg (b1 x),sq_nonneg (b2 x),sq_nonneg (r2 x*b2 x),sq_nonneg (theta x*b2 x),sq_nonneg (v3 x)])

end
end StrongSilver.FourPhase
