-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ScalarRampTrajectory
import StrongSilver.Scalar.SignedIntervals

namespace StrongSilver
open Set Real
noncomputable section
set_option maxHeartbeats 1000000

def scalarBackwardFactor (s b : ℝ) : ℝ := if b ≤ 0 then 1 else (1-s*b)⁻¹
def scalarBackwardProduct (s : ℝ) (h : List ℝ) : ℝ := (h.map (scalarBackwardFactor s)).prod
def scalarNegativeFactor (s b : ℝ) : ℝ := 1+s*max (-b) 0
def scalarNegativeProduct (s : ℝ) (h : List ℝ) : ℝ := (h.map (scalarNegativeFactor s)).prod

namespace ScalarRamp
variable (R : ScalarRamp)

theorem backwardFactor_ge_one {b : ℝ} (hb : R.base*b < 1) : 1 ≤ scalarBackwardFactor R.base b := by
  unfold scalarBackwardFactor
  split_ifs with hneg
  · exact le_rfl
  · have hbpos : 0 < b := lt_of_not_ge hneg
    apply (one_le_inv₀ (by linarith : 0 < 1-R.base*b)).mpr
    nlinarith only [mul_nonneg R.base_nonnegative hbpos.le]

theorem backwardProduct_ge_one (h : List ℝ) (hh : ∀ b ∈ h, R.base*b < 1) :
    1 ≤ scalarBackwardProduct R.base h := by
  induction h with
  | nil => exact le_rfl
  | cons b h ih =>
    have hb := R.backwardFactor_ge_one (hh b List.mem_cons_self)
    have ht := ih (fun c hc => hh c (List.mem_cons_of_mem b hc))
    change 1 ≤ scalarBackwardFactor R.base b*scalarBackwardProduct R.base h
    nlinarith only [hb,ht]

theorem predecessor_factor_upper {b x y : ℝ} (hb : R.base*b < 1) (hx : 0 ≤ x)
    (he : x-b*R.physical x = y) :
    x ≤ scalarBackwardFactor R.base b*(y+R.amplitude*max b 0) := by
  have hu := R.predecessor_upper hx he
  by_cases hneg : b ≤ 0
  · rw [scalarBackwardFactor,if_pos hneg,max_eq_right hneg,mul_zero,add_zero,one_mul]
    exact hu.1 hneg
  · have hpos : 0 < b := lt_of_not_ge hneg
    rw [scalarBackwardFactor,if_neg hneg,max_eq_left hpos.le]
    have hdiv : x ≤ (y+R.amplitude*b)/(1-R.base*b) :=
      (le_div_iff₀ (by linarith : 0 < 1-R.base*b)).mpr (by nlinarith only [hu.2 hpos.le])
    simpa only [div_eq_mul_inv,mul_comm] using hdiv

theorem trajectory_upper (h : List ℝ) (hh : ∀ b ∈ h, R.base*b < 1) (x y : ℝ)
    (hend : iterate h R.physical x = y)
    (hstates : ∀ i : ℕ, i ≤ h.length → 0 < iterate (h.take i) R.physical x) :
    x ≤ scalarBackwardProduct R.base h*(y+R.amplitude*Scalar.SignedIntervals.positiveMass h) := by
  induction h generalizing x with
  | nil => simpa only [scalarBackwardProduct,List.map_nil,List.prod_nil,
      Scalar.SignedIntervals.positiveMass,List.sum_nil,mul_zero,add_zero,one_mul,iterate_nil] using hend.le
  | cons b h ih =>
    have hx : 0 < x := by simpa only [List.take_zero,iterate_nil] using hstates 0 (by omega)
    let z := x-b*R.physical x
    have hzstates : ∀ i : ℕ, i ≤ h.length → 0 < iterate (h.take i) R.physical z := by
      intro i hi
      have hs := hstates (i+1) (by simp only [List.length_cons]; omega)
      simpa only [List.take_succ_cons,iterate_cons,smul_eq_mul] using hs
    have htail := fun c hc => hh c (List.mem_cons_of_mem b hc)
    have hzEnd : iterate h R.physical z = y := by simpa only [iterate_cons,smul_eq_mul] using hend
    have hi := ih htail z hzEnd hzstates
    have hp := R.predecessor_factor_upper (hh b List.mem_cons_self) hx.le (show x-b*R.physical x = z from rfl)
    have hprod := R.backwardProduct_ge_one h htail
    have hf := R.backwardFactor_ge_one (hh b List.mem_cons_self)
    have hpad := mul_nonneg R.amplitude_nonnegative (le_max_right b 0)
    have hhpad := mul_le_mul_of_nonneg_right hprod hpad
    have hmul := mul_le_mul_of_nonneg_left hi (zero_le_one.trans hf)
    change x ≤ (scalarBackwardFactor R.base b*scalarBackwardProduct R.base h)*
      (y+R.amplitude*(max b 0+Scalar.SignedIntervals.positiveMass h))
    have hpadmul := mul_le_mul_of_nonneg_left hhpad (zero_le_one.trans hf)
    nlinarith only [hp,hmul,hpadmul]

theorem min_step_upper {b x : ℝ} (hx : 0 ≤ x) :
    min (x-b*R.physical x) R.threshold ≤ scalarNegativeFactor R.base b*min x R.threshold := by
  have hf : 1 ≤ scalarNegativeFactor R.base b := by
    unfold scalarNegativeFactor
    exact le_add_of_nonneg_right (mul_nonneg R.base_nonnegative (le_max_right _ _))
  by_cases hsmall : x ≤ R.threshold
  · rw [min_eq_left hsmall,R.physical_below_threshold hx hsmall]
    have hstep : x-b*(R.base*x) ≤ scalarNegativeFactor R.base b*x := by
      have hb : -b ≤ max (-b) 0 := le_max_left _ _
      have hm := mul_le_mul_of_nonneg_left hb (mul_nonneg R.base_nonnegative hx)
      unfold scalarNegativeFactor
      nlinarith only [hm]
    exact (min_le_left _ _).trans hstep
  · rw [min_eq_right (le_of_not_ge hsmall)]
    have hm := mul_le_mul_of_nonneg_right hf R.threshold_nonnegative
    simp only [one_mul] at hm
    exact (min_le_right (x-b*R.physical x) R.threshold).trans hm

theorem negativeProduct_ge_one (h : List ℝ) : 1 ≤ scalarNegativeProduct R.base h := by
  induction h with
  | nil => exact le_rfl
  | cons b h ih =>
    have hf : 1 ≤ scalarNegativeFactor R.base b :=
      le_add_of_nonneg_right (mul_nonneg R.base_nonnegative (le_max_right _ _))
    change 1 ≤ scalarNegativeFactor R.base b*scalarNegativeProduct R.base h
    nlinarith only [hf,ih]

theorem trajectory_lower (h : List ℝ) (x y : ℝ)
    (hend : iterate h R.physical x = y)
    (hstates : ∀ i : ℕ, i ≤ h.length → 0 < iterate (h.take i) R.physical x) :
    min y R.threshold ≤ scalarNegativeProduct R.base h*min x R.threshold := by
  induction h generalizing x with
  | nil =>
    have he : x = y := hend
    subst y
    simp only [scalarNegativeProduct,List.map_nil,List.prod_nil,one_mul,iterate_nil,le_refl]
  | cons b h ih =>
    let z := x-b*R.physical x
    have hx : 0 < x := by simpa only [List.take_zero,iterate_nil] using hstates 0 (by omega)
    have hzstates : ∀ i : ℕ, i ≤ h.length → 0 < iterate (h.take i) R.physical z := by
      intro i hi
      have hs := hstates (i+1) (by simp only [List.length_cons]; omega)
      simpa only [List.take_succ_cons,iterate_cons,smul_eq_mul] using hs
    have hzEnd : iterate h R.physical z = y := by simpa only [iterate_cons,smul_eq_mul] using hend
    have hi := ih z hzEnd hzstates
    have hstep := R.min_step_upper (b := b) hx.le
    have hmul := mul_le_mul_of_nonneg_left hstep (zero_le_one.trans (R.negativeProduct_ge_one h))
    change min y R.threshold ≤ (scalarNegativeFactor R.base b*scalarNegativeProduct R.base h)*min x R.threshold
    nlinarith only [hi,hmul]

end ScalarRamp
end
end StrongSilver
