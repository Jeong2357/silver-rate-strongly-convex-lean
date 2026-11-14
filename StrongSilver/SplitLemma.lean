-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.Constants
import StrongSilver.Scalar.PaddedSplit

namespace StrongSilver
noncomputable section

theorem scalar_nu_eq : Scalar.Silver.nu = nu := by
  rw [nu_eq_log_ratio]
  rfl

theorem scalar_rho_eq : Scalar.Silver.rho = rho := rfl

theorem scalar_coefficient_eq : Scalar.Silver.coefficient = splitCoefficient := by
  unfold Scalar.Silver.coefficient splitCoefficient
  rw [scalar_nu_eq]

def splitGain (a b t z : ℝ) : ℝ := Real.log (t*z/(a*b))
def powerDecrease (a b z : ℝ) : ℝ := z^nu-a^nu-b^nu
def splitExcess (a b t z : ℝ) : ℝ :=
  splitCoefficient*t^nu*splitGain a b t z-powerDecrease a b z

theorem split_excess_eq (a b t z : ℝ) :
    splitExcess a b t z = Scalar.Silver.excess a b t z := by
  unfold Scalar.Silver.excess
  rw [scalar_nu_eq, scalar_coefficient_eq]
  unfold splitExcess powerDecrease splitGain Scalar.Silver.gain
  ring

/-- Lemma 3.1: the global signed split inequality and both quantitative estimates. -/
theorem split_stability : ∃ c > 0, ∃ C > 0, ∀ a b t z : ℝ,
    0 < a → 0 < b → 0 < t → a ≤ z → z ≤ a+b+t →
      c*t^nu*min 1 ((Real.log (a/(rho*t)))^2+(Real.log (b/(rho*t)))^2+(a+b+t-z)/t)
        ≤ splitExcess a b t z ∧
      |splitGain a b t z| ≤ C*(1+splitExcess a b t z/t^nu) := by
  obtain ⟨c,hc,C,hC,hbound⟩ := Scalar.Silver.max_plus_excess
  refine ⟨c,hc,C,hC,fun a b t z ha hb ht haz hz => ?_⟩
  simpa only [scalar_nu_eq, scalar_rho_eq, ← split_excess_eq, splitGain, Scalar.Silver.gain] using
    hbound a b t z ha hb ht haz hz

theorem split_excess_nonnegative (a b t z : ℝ)
    (ha : 0 < a) (hb : 0 < b) (ht : 0 < t) (haz : a ≤ z) (hz : z ≤ a+b+t) :
    0 ≤ splitExcess a b t z := by
  obtain ⟨c,hc,C,hC,hbound⟩ := split_stability
  have hcost : 0 ≤ min 1
      ((Real.log (a/(rho*t)))^2+(Real.log (b/(rho*t)))^2+(a+b+t-z)/t) := by
    exact le_min zero_le_one (add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _))
      (div_nonneg (by linarith) ht.le))
  exact (mul_nonneg (mul_nonneg hc.le (Real.rpow_nonneg ht.le nu)) hcost).trans
    (hbound a b t z ha hb ht haz hz).1

theorem split_power_decrease_le (a b t z : ℝ)
    (ha : 0 < a) (hb : 0 < b) (ht : 0 < t) (haz : a ≤ z) (hz : z ≤ a+b+t) :
    powerDecrease a b z ≤ splitCoefficient*t^nu*splitGain a b t z := by
  have h := split_excess_nonnegative a b t z ha hb ht haz hz
  exact sub_nonneg.mp h

end
end StrongSilver
