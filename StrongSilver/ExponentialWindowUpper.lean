-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ExponentialStepIntegral

namespace StrongSilver
open Real Set MeasureTheory
noncomputable section
set_option maxHeartbeats 5000000

def exponentialWindow (v lo hi y : ℝ) : ℝ :=
  (if y < hi then Real.exp (v*y) else 0)-(if y < lo then Real.exp (v*y) else 0)

theorem exponentialWindow_eq (v lo hi y : ℝ) (hlo : lo ≤ hi) :
    exponentialWindow v lo hi y = if lo ≤ y ∧ y < hi then Real.exp (v*y) else 0 := by
  by_cases hyl : y < lo
  · have hyh := hyl.trans_le hlo
    simp only [exponentialWindow,hyl,hyh,not_le_of_gt hyl,false_and,↓reduceIte,sub_self]
  · by_cases hyh : y < hi
    · simp only [exponentialWindow,hyl,hyh,le_of_not_gt hyl,and_self,↓reduceIte,sub_zero]
    · simp only [exponentialWindow,hyl,hyh,and_false,↓reduceIte,sub_self]

theorem exponentialWindow_nonnegative (v lo hi y : ℝ) (hlo : lo ≤ hi) : 0 ≤ exponentialWindow v lo hi y := by
  rw [exponentialWindow_eq v lo hi y hlo]
  split_ifs
  · exact (Real.exp_pos _).le
  · exact le_rfl

theorem exponentialWindow_integrable (v lo hi a b : ℝ) : IntervalIntegrable (exponentialWindow v lo hi) volume a b :=
  (exponential_step_intervalIntegrable v hi a b).sub (exponential_step_intervalIntegrable v lo a b)

theorem exponentialWindow_integral (v lo hi a b : ℝ) (hab : a ≤ b) (hal : a ≤ lo) (hlh : lo ≤ hi) (hhb : hi ≤ b) :
    v*(∫ y in a..b, exponentialWindow v lo hi y) = Real.exp (v*hi)-Real.exp (v*lo) := by
  have h1 := exponential_step_integral v a b hi hab
  have h2 := exponential_step_integral v a b lo hab
  rw [min_eq_right hhb,min_eq_left (hal.trans hlh)] at h1
  rw [min_eq_right (hlh.trans hhb),min_eq_left hal] at h2
  unfold exponentialWindow
  rw [intervalIntegral.integral_sub (exponential_step_intervalIntegrable v hi a b) (exponential_step_intervalIntegrable v lo a b)]
  linear_combination h1-h2

/-- A finite weighted interval has at most its length times its
largest exponential value, even when the integration interval cuts it. -/
theorem exponentialWindow_integral_upper (v lo hi a b : ℝ) (hv : 0 < v) (hlo : lo ≤ hi) (hab : a ≤ b) :
    (∫ y in a..b, exponentialWindow v lo hi y) ≤ (hi-lo)*Real.exp (v*hi) := by
  let aa := min a lo
  let bb := max b hi
  have hOuter : aa ≤ bb := (min_le_left _ _).trans (hab.trans (le_max_left _ _))
  have hSub := intervalIntegral.integral_mono_interval (min_le_left a lo) hab (le_max_left b hi)
    (Filter.Eventually.of_forall (fun y => exponentialWindow_nonnegative v lo hi y hlo)) (exponentialWindow_integrable v lo hi aa bb)
  have hFull := exponentialWindow_integral v lo hi aa bb hOuter (min_le_right _ _) hlo (le_max_right _ _)
  have hExp := scaled_exponential_integral v lo hi
  have hEq : (∫ y in aa..bb, exponentialWindow v lo hi y) = (∫ y in lo..hi, Real.exp (v*y)) := by
    exact mul_left_cancel₀ hv.ne' (hFull.trans hExp.symm)
  have hIntExp : IntervalIntegrable (fun y : ℝ => Real.exp (v*y)) volume lo hi :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable lo hi
  have hUpper := intervalIntegral.integral_mono_on hlo hIntExp intervalIntegrable_const (by
    intro y hy
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hy.2 hv.le))
  simp only [intervalIntegral.integral_const,smul_eq_mul] at hUpper
  rw [hEq] at hSub
  exact hSub.trans hUpper

end
end StrongSilver
