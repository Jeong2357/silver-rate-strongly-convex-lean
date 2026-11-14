-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseFeet
import StrongSilver.FourPhaseSlopeProducts

namespace StrongSilver.FourPhase
noncomputable section
set_option maxHeartbeats 3000000

def foot (x : Shape) : Fin 4 → Coordinates := ![foot0 x,foot1 x,foot2 x,foot3 x]

variable {x : Shape} (R : Regular x)
include R

theorem foot0_tie1 : inner ℝ (foot0 x) (slope0 x-slope1 x) = 0 := by
  have hj := V_orthogonal_join R
  rw [real_inner_comm] at hj
  have hf : inner ℝ (foot1 x) (slope0 x-slope1 x) = 0 := by
    have h0 := foot1_common R 0
    have h1 := foot1_common R 1
    change inner ℝ (foot1 x) (slope0 x) = _ at h0
    change inner ℝ (foot1 x) (slope1 x) = _ at h1
    rw [inner_sub_right,h0,h1,sub_self]
  rw [foot0_eq,add_assoc,inner_add_left,hf,hj,zero_add]

theorem negative_e2_coefficient : x 4*r2 x-x 1*theta x < 0 := by
  have h0 := mul_lt_mul_of_pos_left R.r2_lt_one R.k0_positive
  have h1 := mul_lt_mul_of_pos_left R.theta_gt_one R.m1_positive
  nlinarith only [h0,h1,R.m1_gt_k0]

theorem foot0_comparison12 : inner ℝ (foot0 x) (slope1 x-slope2 x) =
    -(1+theta x)*(x 4*r2 x-x 1*theta x)*b2sq x := by
  rw [foot0_eq,foot1_formula R]
  simp only [slope0,slope1,slope2,point_smul,point_add,point_sub,point_inner]
  linear_combination -(1+theta x)*(x 4*r2 x-x 1*theta x)*(b2_sq R)

theorem foot0_comparison13 : inner ℝ (foot0 x) (slope1 x-slope3 x) =
    (x 4+x 1)*bodyScale x/upperTime x-theta x*(x 4*r2 x-x 1*theta x)*b2sq x := by
  have hi := a_b1_identity R
  have hf : inner ℝ (foot1 x) (slope1 x-slope3 x) = 0 := by
    have h1 := foot1_common R 1
    have h3 := foot1_common R 3
    change inner ℝ (foot1 x) (slope1 x) = _ at h1
    change inner ℝ (foot1 x) (slope3 x) = _ at h3
    rw [inner_sub_right,h1,h3,sub_self]
  rw [foot0_eq,inner_add_left,inner_add_left,real_inner_smul_left,real_inner_smul_left,hf]
  simp only [slope0,slope1,slope3,point_sub,point_inner]
  linear_combination (x 4+x 1)*hi+(x 4+x 1)*(b1_sq R)-
    theta x*(x 4*r2 x-x 1*theta x)*(b2_sq R)

theorem foot0_above (j : Fin 4) : 0 ≤ inner ℝ (foot0 x) (slope0 x-slope x j) := by
  have ht : 0 < theta x := zero_lt_one.trans R.theta_gt_one
  have hn := negative_e2_coefficient R
  have hb := R.b2sq_positive
  have hf := foot0_tie1 R
  fin_cases j
  all_goals simp only [slope,Matrix.cons_val_zero',Matrix.cons_val_succ']
  · simp only [sub_self,inner_zero_right,le_refl]
  · exact hf.ge
  · have hh := foot0_comparison12 R
    have he : inner ℝ (foot0 x) (slope0 x-slope2 x) =
        inner ℝ (foot0 x) (slope0 x-slope1 x)+inner ℝ (foot0 x) (slope1 x-slope2 x) := by
      simp only [inner_sub_right]; ring
    rw [he,hf,hh,zero_add]
    exact mul_nonneg (mul_nonneg_of_nonpos_of_nonpos (by linarith only [ht]) hn.le) hb.le
  · have hh := foot0_comparison13 R
    have he : inner ℝ (foot0 x) (slope0 x-slope3 x) =
        inner ℝ (foot0 x) (slope0 x-slope1 x)+inner ℝ (foot0 x) (slope1 x-slope3 x) := by
      simp only [inner_sub_right]; ring
    rw [he,hf,hh,zero_add]
    have hpos := div_pos (mul_pos (add_pos R.k0_positive R.m1_positive) R.bodyScale_positive) R.upperTime_positive
    have hneg := mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos ht.le hn.le) hb.le
    linarith only [hpos,hneg]

theorem foot_dominates (hz : 0 ≤ x 7) (i j : Fin 4) :
    0 ≤ inner ℝ (foot x i) (slope x i-slope x j) := by
  fin_cases i
  · change 0 ≤ inner ℝ (foot0 x) (slope0 x-slope x j)
    exact foot0_above R j
  · change 0 ≤ inner ℝ (foot1 x) (slope1 x-slope x j)
    have hi := foot1_common R 1
    have hj := foot1_common R j
    change inner ℝ (foot1 x) (slope1 x) = _ at hi
    change inner ℝ (foot1 x) (slope x j) = _ at hj
    rw [inner_sub_right,hi,hj,sub_self]
  · change 0 ≤ inner ℝ (foot2 x) (slope2 x-slope x j)
    fin_cases j
    all_goals simp only [slope,Matrix.cons_val_zero',Matrix.cons_val_succ']
    · rw [foot2_above0 R]
      exact mul_nonneg (mul_nonneg R.k2_positive.le (sub_nonneg.mpr R.r2_lt_one.le)) R.b2sq_positive.le
    · rw [foot2_above1 R]
      have ht : 0 < theta x := zero_lt_one.trans R.theta_gt_one
      exact mul_nonneg (mul_nonneg R.k2_positive.le (by linarith only [ht])) R.b2sq_positive.le
    · simp only [sub_self,inner_zero_right,le_refl]
    · exact (foot2_tie3 R).ge
  · change 0 ≤ inner ℝ (foot3 x) (slope3 x-slope x j)
    rw [foot3_formula]
    fin_cases j
    all_goals simp only [slope,Matrix.cons_val_zero',Matrix.cons_val_succ',slope0,slope1,slope2,slope3,point_sub,point_inner]
    all_goals nlinarith only [mul_nonneg hz R.a_positive.le,hz]

/-- All affine comparisons hold along the entire backward ray of each
phase, including every positive rescaling used by the product change of time. -/
theorem query_dominates (hz : 0 ≤ x 7) (i j : Fin 4) {s c : ℝ} (hs : 0 ≤ s) (hc : 0 ≤ c) :
    inner ℝ (slope x j) (c • (foot x i+s • slope x i)) ≤
      inner ℝ (slope x i) (c • (foot x i+s • slope x i)) := by
  have hf := foot_dominates R hz i j
  have hg := slope_self_difference_nonnegative R i j
  have hh : 0 ≤ inner ℝ (foot x i+s • slope x i) (slope x i-slope x j) := by
    rw [inner_add_left,real_inner_smul_left]
    exact add_nonneg hf (mul_nonneg hs hg)
  have hh' := mul_nonneg hc hh
  rw [inner_sub_right] at hh'
  simp only [real_inner_smul_right,real_inner_comm (foot x i+s • slope x i)]
  nlinarith only [hh']

end
end StrongSilver.FourPhase
