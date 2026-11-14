-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseComparisons

namespace StrongSilver.FourPhase
noncomputable section
set_option maxHeartbeats 4000000

variable {x : Shape} (R : Regular x)
include R

theorem source_slope_difference : inner ℝ (source x) (slope0 x-slope1 x) =
    x 0*(x 1/x 4)*theta x*(r2 x+theta x)*b2sq x := by
  have hX : source x = foot0 x+x 0 • slope0 x := by
    rw [foot0]; exact (sub_add_cancel _ _).symm
  calc
    inner ℝ (source x) (slope0 x-slope1 x) =
        inner ℝ (foot0 x) (slope0 x-slope1 x)+
        x 0*inner ℝ (slope0 x) (slope0 x-slope1 x) := by
      rw [hX,inner_add_left,real_inner_smul_left]
    _ = _ := by rw [foot0_tie1 R,slope01_difference R]; ring

theorem r2_theta_identity : t0 x*(r2 x+theta x)*b2sq x =
    leftMass x*bodyScale x*x 2/(x 5*x 6) := by
  have hr := r2_identity x R.t0_positive.ne' R.b2sq_positive.ne'
  have hb := b1sq_identity x R.totalTime_positive.ne' R.upperTime_positive.ne'
  have hmid : t0 x*(r2 x+theta x)*b2sq x =
      leftMass x*theta x*b2sq x-totalTime x*b1sq x := by
    unfold leftMass t0 at hr ⊢
    linear_combination hr
  rw [hmid,hb]
  unfold theta b2sq
  have hk1 := R.k1_positive.ne'
  have hk2 := R.k2_positive.ne'
  have hU := R.upperTime_positive.ne'
  field_simp
  unfold upperTime t2
  ring

omit R in
theorem source_decomposition : source x = t0 x • slope0 x+t1 x • slope1 x+
    t2 x • slope2 x+q x • slope3 x := by
  have h3 : start3 x = q x • slope3 x := by
    simp only [start3,slope3,point_smul]; congr 1 <;> ring
  unfold source start1 start2
  rw [h3]
  module

theorem source_norm_moments : ‖source x‖^2 =
    (t0 x+t1 x)*inner ℝ (source x) (slope1 x)+
    t0 x*inner ℝ (source x) (slope0 x-slope1 x) := by
  calc
    ‖source x‖^2 = inner ℝ (source x) (t0 x • slope0 x+t1 x • slope1 x+
        t2 x • slope2 x+q x • slope3 x) := by
      rw [← source_decomposition,real_inner_self_eq_norm_sq]
    _ = _ := by
      simp only [inner_add_right,real_inner_smul_right,source_slope2_inner R,
        source_slope3_inner R,inner_sub_right]
      ring

theorem source_norm_formula : ‖source x‖^2 =
    (leftMass x*bodyScale x/x 5)*(leftMass x+x 5+
      x 0*x 1*x 2*t2 x/(x 4*x 5*x 6)) := by
  rw [source_norm_moments R,source_slope1_formula R,source_slope_difference R]
  have ht : t0 x+t1 x = leftMass x+x 5 := by unfold t0 t1 leftMass; ring
  rw [ht]
  have hh := r2_theta_identity R
  have hmul : t0 x*(x 0*(x 1/x 4)*theta x*(r2 x+theta x)*b2sq x) =
      (x 0*(x 1/x 4)*theta x)*(leftMass x*bodyScale x*x 2/(x 5*x 6)) := by
    linear_combination (x 0*(x 1/x 4)*theta x)*hh
  rw [hmul]
  unfold theta
  have hk0 := R.k0_positive.ne'
  have hk1 := R.k1_positive.ne'
  have hk2 := R.k2_positive.ne'
  field_simp
  <;> ring

end
end StrongSilver.FourPhase
