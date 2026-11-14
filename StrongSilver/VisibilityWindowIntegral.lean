-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ExponentialStepIntegral

namespace StrongSilver
open Real Set MeasureTheory
noncomputable section
set_option maxHeartbeats 3600000

def visibilityWindowKernel (v s z y : ℝ) : ℝ :=
  (if y < z+2*s then Real.exp (v*y) else 0)-(if y < z+s then Real.exp (v*y) else 0)

theorem visibilityWindowKernel_eq (v s z y : ℝ) (hs : 0 ≤ s) :
    visibilityWindowKernel v s z y = if z+s ≤ y ∧ y < z+2*s then Real.exp (v*y) else 0 := by
  unfold visibilityWindowKernel
  by_cases hlo : y < z+s
  · have hhi : y < z+2*s := by linarith only [hlo,hs]
    simp only [hlo,hhi,not_le_of_gt hlo,false_and,↓reduceIte,sub_self]
  · by_cases hhi : y < z+2*s
    · simp only [hlo,hhi,le_of_not_gt hlo,and_self,↓reduceIte,sub_zero]
    · simp only [hlo,hhi,and_false,↓reduceIte,sub_self]

theorem visibilityWindowKernel_integrable (v s z a b : ℝ) :
    IntervalIntegrable (visibilityWindowKernel v s z) volume a b :=
  (exponential_step_intervalIntegrable v (z+2*s) a b).sub (exponential_step_intervalIntegrable v (z+s) a b)

def visibilityWindowFactor (v s : ℝ) : ℝ := Real.exp (2*v*s)-Real.exp (v*s)

theorem visibilityWindowFactor_positive {v s : ℝ} (hv : 0 < v) (hs : 0 < s) :
    0 < visibilityWindowFactor v s := by
  unfold visibilityWindowFactor
  apply sub_pos.mpr
  apply Real.exp_lt_exp.mpr
  nlinarith only [mul_pos hv hs]

theorem visibilityWindowKernel_integral (v s z a b : ℝ) (hab : a ≤ b) (hs : 0 ≤ s)
    (hlo : a ≤ z+s) (hhi : z+2*s ≤ b) :
    v*(∫ y in a..b, visibilityWindowKernel v s z y) = visibilityWindowFactor v s*Real.exp (v*z) := by
  have horder : z+s ≤ z+2*s := by linarith only [hs]
  have h1 := exponential_step_integral v a b (z+2*s) hab
  have h2 := exponential_step_integral v a b (z+s) hab
  rw [min_eq_right hhi,min_eq_left (hlo.trans horder)] at h1
  rw [min_eq_right (horder.trans hhi),min_eq_left hlo] at h2
  have hI : (∫ y in a..b, visibilityWindowKernel v s z y) =
      (∫ y in a..b, if y < z+2*s then Real.exp (v*y) else 0)-
        (∫ y in a..b, if y < z+s then Real.exp (v*y) else 0) :=
    intervalIntegral.integral_sub (exponential_step_intervalIntegrable v (z+2*s) a b)
      (exponential_step_intervalIntegrable v (z+s) a b)
  rw [hI]
  have he1 : Real.exp (v*(z+2*s)) = Real.exp (v*z)*Real.exp (2*v*s) := by rw [show v*(z+2*s) = v*z+2*v*s by ring,Real.exp_add]
  have he2 : Real.exp (v*(z+s)) = Real.exp (v*z)*Real.exp (v*s) := by rw [mul_add,Real.exp_add]
  rw [he1] at h1
  rw [he2] at h2
  unfold visibilityWindowFactor
  linear_combination h1-h2

def visibilityKernelSum {α : Type*} (height score : α → ℝ) (v s : ℝ) (events : List α) (y : ℝ) : ℝ :=
  (events.map fun e => score e*visibilityWindowKernel v s (height e) y).sum

theorem visibilityKernelSum_integrable {α : Type*} (height score : α → ℝ) (v s a b : ℝ) (events : List α) :
    IntervalIntegrable (visibilityKernelSum height score v s events) volume a b := by
  induction events with
  | nil => exact intervalIntegrable_const
  | cons e es ih =>
    change IntervalIntegrable (fun y => score e*visibilityWindowKernel v s (height e) y+visibilityKernelSum height score v s es y) volume a b
    exact ((visibilityWindowKernel_integrable v s (height e) a b).const_mul (score e)).add ih

theorem visibilityKernelSum_integral {α : Type*} (height score : α → ℝ) (v s a b : ℝ) (events : List α)
    (hab : a ≤ b) (hs : 0 ≤ s)
    (hwindow : ∀ e ∈ events, a ≤ height e+s ∧ height e+2*s ≤ b) :
    v*(∫ y in a..b, visibilityKernelSum height score v s events y) =
      visibilityWindowFactor v s*(events.map fun e => Real.exp (v*height e)*score e).sum := by
  induction events with
  | nil => simp [visibilityKernelSum]
  | cons e es ih =>
    have he := hwindow e (by simp)
    have hi := ih (fun q hq => hwindow q (List.mem_cons_of_mem e hq))
    have hp := visibilityWindowKernel_integral v s (height e) a b hab hs he.1 he.2
    have hEq : visibilityKernelSum height score v s (e::es) = fun y =>
        score e*visibilityWindowKernel v s (height e) y+visibilityKernelSum height score v s es y := rfl
    rw [hEq,intervalIntegral.integral_add ((visibilityWindowKernel_integrable v s (height e) a b).const_mul (score e))
      (visibilityKernelSum_integrable height score v s a b es),intervalIntegral.integral_const_mul]
    simp only [List.map_cons,List.sum_cons]
    linear_combination hi+score e*hp

/-- A finite weighted visibility bound. Its hypotheses are pointwise
cutoff domination and containment of the fixed-width visibility
intervals; no interchange of an infinite sum and an integral is used. -/
theorem finite_visibility_integral_budget {α : Type*} (height score : α → ℝ) (v s a b : ℝ) (events : List α)
    (B : ℝ → ℝ) (hab : a ≤ b) (hv : 0 ≤ v) (hs : 0 ≤ s)
    (hwindow : ∀ e ∈ events, a ≤ height e+s ∧ height e+2*s ≤ b)
    (hB : IntervalIntegrable B volume a b)
    (hpoint : ∀ y ∈ Icc a b, visibilityKernelSum height score v s events y ≤ B y) :
    visibilityWindowFactor v s*(events.map fun e => Real.exp (v*height e)*score e).sum ≤ v*(∫ y in a..b, B y) := by
  have hi := intervalIntegral.integral_mono_on hab (visibilityKernelSum_integrable height score v s a b events) hB hpoint
  have hh := mul_le_mul_of_nonneg_left hi hv
  rwa [visibilityKernelSum_integral height score v s a b events hab hs hwindow] at hh

end
end StrongSilver
