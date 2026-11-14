-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.Scalar.MaxPlusUnitGain

namespace StrongSilver.Scalar.Silver
noncomputable section
set_option maxHeartbeats 1000000

def gain (a b t z : ℝ) : ℝ := Real.log (t*z/(a*b))
def excess (a b t z : ℝ) : ℝ := a^nu+b^nu-z^nu+coefficient*t^nu*gain a b t z

theorem gain_normalize (a b t z : ℝ) (ht : 0 < t) :
    unitGain (a/t) (b/t) (z/t)=gain a b t z := by
  unfold unitGain gain
  congr 1
  field_simp [ht.ne'] <;> ring

theorem excess_normalize (a b t z : ℝ) (ha : 0 < a) (hb : 0 < b) (ht : 0 < t) (hz : 0 < z) :
    unitExcess (a/t) (b/t) (z/t)=excess a b t z/t^nu := by
  rw [unitExcess_formula _ _ _ (div_pos ha ht) (div_pos hb ht) (div_pos hz ht),gain_normalize a b t z ht]
  unfold powerDefect excess
  rw [Real.div_rpow ha.le ht.le,Real.div_rpow hb.le ht.le,Real.div_rpow hz.le ht.le]
  have htPow : t^nu ≠ 0 := (Real.rpow_pos_of_pos ht nu).ne'
  field_simp <;> ring

theorem normalized_cost (a b t z : ℝ) (ht : 0 < t) :
    logDistance (a/t) (b/t)+((a/t)+(b/t)+1-z/t)=
      (Real.log (a/(rho*t)))^2+(Real.log (b/(rho*t)))^2+(a+b+t-z)/t := by
  unfold logDistance
  rw [show (a/t)/rho=a/(rho*t) by ring,show (b/t)/rho=b/(rho*t) by ring]
  have he : a/t+b/t+1-z/t=(a+b+t-z)/t := by field_simp [ht.ne'] <;> ring
  exact congrArg (fun s : ℝ => (Real.log (a/(rho*t)))^2+(Real.log (b/(rho*t)))^2+s) he

end
end StrongSilver.Scalar.Silver
