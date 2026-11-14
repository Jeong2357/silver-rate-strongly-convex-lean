-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseParameters

namespace StrongSilver.FourPhase
noncomputable section
set_option maxHeartbeats 2000000

/-- Open scalar conditions that make the explicit four-slope geometry
well defined. They will be discharged near the reference configuration. -/
structure Regular (x : Shape) : Prop where
  m0_positive : 0 < x 0
  m1_positive : 0 < x 1
  m2_positive : 0 < x 2
  m3_positive : 0 < x 3
  k0_positive : 0 < x 4
  k1_positive : 0 < x 5
  k2_positive : 0 < x 6
  q_positive : 0 < q x
  theta_gt_one : 1 < theta x
  r2_positive : 0 < r2 x
  r2_lt_one : r2 x < 1
  m1_gt_k0 : x 4 < x 1

namespace Regular
variable {x : Shape} (R : Regular x)
include R

theorem t0_positive : 0 < t0 x := add_pos R.m0_positive R.k0_positive
theorem t1_positive : 0 < t1 x := add_pos R.m1_positive R.k1_positive
theorem t2_positive : 0 < t2 x := add_pos R.m2_positive R.k2_positive

theorem totalTime_positive : 0 < totalTime x := add_pos (add_pos R.t0_positive R.t1_positive) R.t2_positive

theorem upperTime_positive : 0 < upperTime x := add_pos R.k1_positive R.t2_positive

theorem leftMass_positive : 0 < leftMass x := add_pos (add_pos R.m0_positive R.k0_positive) R.m1_positive

theorem rightMass_positive : 0 < rightMass x := add_pos (add_pos R.m2_positive R.k2_positive) R.m3_positive

theorem totalMass_positive : 0 < totalMass x := add_pos (add_pos R.leftMass_positive R.k1_positive) R.rightMass_positive

theorem a_positive : 0 < a x := div_pos R.q_positive R.totalTime_positive

theorem bodyScale_positive : 0 < bodyScale x := mul_pos (by have hh := R.a_positive; linarith only [hh]) R.q_positive

theorem b1sq_positive : 0 < b1sq x := by
  have hTU : upperTime x < totalTime x := by
    have hh := totalTime_sub_upperTime x
    have hp := R.leftMass_positive
    linarith only [hh,hp]
  have hi := one_div_lt_one_div_of_lt R.upperTime_positive hTU
  exact mul_pos R.bodyScale_positive (sub_pos.mpr hi)

theorem b2sq_positive : 0 < b2sq x := by
  have hkU : x 6 < upperTime x := by
    unfold upperTime t2
    linarith only [R.k1_positive,R.m2_positive]
  have hi := one_div_lt_one_div_of_lt R.k2_positive hkU
  exact mul_pos R.bodyScale_positive (sub_pos.mpr hi)

theorem v3sq_positive : 0 < v3sq x := by
  have hk : 1 < x 1/x 4 := (one_lt_div R.k0_positive).mpr R.m1_gt_k0
  have ht : 0 < theta x := zero_lt_one.trans R.theta_gt_one
  have hm := mul_lt_mul_of_pos_right hk ht
  have hgap : 0 < (x 1/x 4)*theta x-r2 x := by nlinarith only [hm,R.theta_gt_one,R.r2_lt_one]
  have hsum : 0 < r2 x+theta x := add_pos R.r2_positive ht
  rw [v3sq_factor]
  exact mul_pos (mul_pos hsum hgap) R.b2sq_positive

end Regular
end
end StrongSilver.FourPhase
