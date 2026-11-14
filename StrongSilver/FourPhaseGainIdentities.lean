-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseReference
import StrongSilver.FourPhaseRegular

namespace StrongSilver.FourPhase
noncomputable section
set_option maxHeartbeats 3000000

variable {x : Shape} (R : Regular x)
include R

theorem exp_neg_gain : Real.exp (-gain x) = leftMass x*rightMass x/(x 5*totalMass x) := by
  have hp : 0 < x 5*totalMass x/(leftMass x*rightMass x) :=
    div_pos (mul_pos R.k1_positive R.totalMass_positive) (mul_pos R.leftMass_positive R.rightMass_positive)
  rw [gain,Real.exp_neg,Real.exp_log hp,inv_div]

theorem exp_neg_gainLeft : Real.exp (-gainLeft x) = x 0*x 1/(x 4*leftMass x) := by
  have hp : 0 < x 4*leftMass x/(x 0*x 1) :=
    div_pos (mul_pos R.k0_positive R.leftMass_positive) (mul_pos R.m0_positive R.m1_positive)
  rw [gainLeft,Real.exp_neg,Real.exp_log hp,inv_div]

theorem exp_neg_gainRight : Real.exp (-gainRight x) = x 2*x 3/(x 6*rightMass x) := by
  have hp : 0 < x 6*rightMass x/(x 2*x 3) :=
    div_pos (mul_pos R.k2_positive R.rightMass_positive) (mul_pos R.m2_positive R.m3_positive)
  rw [gainRight,Real.exp_neg,Real.exp_log hp,inv_div]

theorem exp_neg_three_gains : Real.exp (-gain x-gainLeft x-gainRight x) =
    x 0*x 1*x 2*x 3/(x 4*x 5*x 6*totalMass x) := by
  simp only [sub_eq_add_neg,Real.exp_add,exp_neg_gain R,exp_neg_gainLeft R,exp_neg_gainRight R]
  have hL := R.leftMass_positive.ne'
  have hR := R.rightMass_positive.ne'
  have hM := R.totalMass_positive.ne'
  have hk0 := R.k0_positive.ne'
  have hk1 := R.k1_positive.ne'
  have hk2 := R.k2_positive.ne'
  field_simp
  <;> ring

omit R in
theorem mass_product_identity : x 3*(leftMass x+x 5) =
    rightMass x*totalTime x-totalMass x*t2 x := by
  dsimp only [totalMass,totalTime,leftMass,rightMass,t0,t1,t2]
  ring

omit R in
/-- The coefficient multiplying the combined gain at exact balance. -/
theorem gainCoefficient_reference_sqrt : gainCoefficient reference = 1/Real.sqrt 2 := by
  rw [gainCoefficient_reference]
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hp := Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)
  unfold rho
  field_simp
  nlinarith only [hs]

end
end StrongSilver.FourPhase
