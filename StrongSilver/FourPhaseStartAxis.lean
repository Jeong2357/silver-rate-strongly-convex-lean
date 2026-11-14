-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseOrbitQueries

namespace StrongSilver.FourPhase
noncomputable section
set_option maxHeartbeats 1800000

theorem first_starts_axis_nonpositive {x : Shape} (R : Regular x) (i : Fin 3) :
    inner ℝ axis (phaseStart x i.castSucc) ≤ 0 := by
  have ha := R.a_positive
  have hg0 : inner ℝ (slope0 x) axis = a x := point_inner_axis _ _ _ _
  have hg1 : inner ℝ (slope1 x) axis = a x := point_inner_axis _ _ _ _
  have h0 := source_orthogonal_axis R
  have h1 : inner ℝ (start1 x) axis = -t0 x*a x := by
    unfold source at h0
    rw [inner_add_left,real_inner_smul_left,hg0] at h0
    linarith only [h0]
  have h2 : inner ℝ (start2 x) axis = -(t0 x+t1 x)*a x := by
    unfold start1 at h1
    rw [inner_add_left,real_inner_smul_left,hg1] at h1
    nlinarith only [h1]
  fin_cases i
  · change inner ℝ axis (source x) ≤ 0
    rw [real_inner_comm (source x) axis,source_orthogonal_axis R]
  · change inner ℝ axis (start1 x) ≤ 0
    rw [real_inner_comm (start1 x) axis,h1]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr R.t0_positive.le) ha.le
  · change inner ℝ axis (start2 x) ≤ 0
    rw [real_inner_comm (start2 x) axis,h2]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (add_pos R.t0_positive R.t1_positive).le) ha.le

end
end StrongSilver.FourPhase
