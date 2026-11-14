-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseNorm

namespace StrongSilver.FourPhase
noncomputable section
set_option maxHeartbeats 3200000

variable {x : Shape} (R : Regular x)
include R

theorem source_slope1_positive : 0 < inner ℝ (source x) (slope1 x) := by
  rw [source_slope1_formula R]
  exact div_pos (mul_pos R.leftMass_positive R.bodyScale_positive) R.k1_positive

theorem source_slope_difference_nonnegative : 0 ≤ inner ℝ (source x) (slope0 x-slope1 x) := by
  rw [source_slope_difference R]
  have ht : 0 < theta x := zero_lt_one.trans R.theta_gt_one
  exact (mul_pos (mul_pos (mul_pos (mul_pos R.m0_positive (div_pos R.m1_positive R.k0_positive)) ht)
    (add_pos R.r2_positive ht)) R.b2sq_positive).le

theorem source_slope0_positive : 0 < inner ℝ (source x) (slope0 x) := by
  have h1 := source_slope1_positive R
  have hd := source_slope_difference_nonnegative R
  rw [inner_sub_right] at hd
  linarith only [h1,hd]

theorem source_slopes_nonnegative (i : Fin 4) : 0 ≤ inner ℝ (source x) (slope x i) := by
  fin_cases i
  · exact (source_slope0_positive R).le
  · exact (source_slope1_positive R).le
  · exact (source_slope2_inner R).ge
  · exact (source_slope3_inner R).ge

theorem source_slopes_upper (ht0 : 1 ≤ t0 x) (ht1 : 1 ≤ t1 x) (i : Fin 4) :
    inner ℝ (source x) (slope x i) ≤ ‖source x‖^2 := by
  have h0 := source_slope0_positive R
  have h1 := source_slope1_positive R
  have hd := source_slope_difference_nonnegative R
  have hnorm := source_norm_moments R
  have hp0 := mul_nonneg (sub_nonneg.mpr ht0) hd
  have hp1 := mul_nonneg (show 0 ≤ t0 x+t1 x-1 by linarith only [ht0,ht1]) h1.le
  rw [inner_sub_right] at hd hnorm hp0
  fin_cases i
  · change inner ℝ (source x) (slope0 x) ≤ _
    nlinarith only [hnorm,hp0,hp1]
  · change inner ℝ (source x) (slope1 x) ≤ _
    have hpd := mul_nonneg R.t0_positive.le hd
    nlinarith only [hnorm,hp1,hpd]
  · change inner ℝ (source x) (slope2 x) ≤ _
    rw [source_slope2_inner R]; positivity
  · change inner ℝ (source x) (slope3 x) ≤ _
    rw [source_slope3_inner R]; positivity

theorem source_foot1 : inner ℝ (source x) (foot1 x) = x 5*inner ℝ (source x) (slope1 x) := by
  have he : foot1 x = start3 x+t2 x • slope2 x+x 5 • slope1 x := by
    unfold foot1 start1 start2 t1
    module
  rw [he,inner_add_right,inner_add_right,real_inner_smul_right,real_inner_smul_right,
    source_slope2_inner R]
  have haxis : start3 x = -q x • axis := by simp only [start3,axis,point_smul]; congr 1 <;> ring
  rw [haxis,real_inner_smul_right,source_orthogonal_axis R]
  ring

theorem source_foot2 : inner ℝ (source x) (foot2 x) = 0 := by
  have he : foot2 x = start3 x+x 6 • slope2 x := by unfold foot2 start2 t2; module
  have haxis : start3 x = -q x • axis := by simp only [start3,axis,point_smul]; congr 1 <;> ring
  rw [he,haxis,inner_add_right,real_inner_smul_right,real_inner_smul_right,
    source_slope2_inner R,source_orthogonal_axis R]
  ring

theorem source_foot3 : inner ℝ (source x) (foot3 x) = 0 := by
  have he : foot3 x = -x 7 • axis := by
    rw [foot3_formula,axis,point_smul]; congr 1 <;> ring
  rw [he,real_inner_smul_right,source_orthogonal_axis R,mul_zero]

theorem source_feet_nonnegative (i : Fin 4) : 0 ≤ inner ℝ (source x) (foot x i) := by
  fin_cases i
  · change 0 ≤ inner ℝ (source x) (foot0 x)
    rw [foot0_eq,inner_add_right,inner_add_right,real_inner_smul_right,real_inner_smul_right,source_foot1 R]
    exact add_nonneg (add_nonneg (mul_nonneg R.k1_positive.le (source_slope1_positive R).le)
      (mul_nonneg R.k0_positive.le (source_slope0_positive R).le))
      (mul_nonneg R.m1_positive.le (source_slope1_positive R).le)
  · exact (source_foot1 R ▸ mul_nonneg R.k1_positive.le (source_slope1_positive R).le)
  · exact (source_foot2 R).ge
  · exact (source_foot3 R).ge

theorem source_queries_nonnegative (i : Fin 4) {s c : ℝ} (hs : 0 ≤ s) (hc : 0 ≤ c) :
    0 ≤ inner ℝ (source x) (c • (foot x i+s • slope x i)) := by
  rw [real_inner_smul_right,inner_add_right,real_inner_smul_right]
  exact mul_nonneg hc (add_nonneg (source_feet_nonnegative R i) (mul_nonneg hs (source_slopes_nonnegative R i)))

end
end StrongSilver.FourPhase
