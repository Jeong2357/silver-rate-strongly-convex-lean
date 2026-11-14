-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ExponentialStepIntegral

namespace StrongSilver
open Real MeasureTheory
noncomputable section
set_option maxHeartbeats 3600000

/-- A finite step observable with its after-jump value at each height. -/
def stepObservable {α : Type*} (height gain : α → ℝ) (base : ℝ) : List α → ℝ → ℝ
  | [], _ => base
  | e::es, y => stepObservable height gain base es y-(if y < height e then gain e else 0)

theorem weighted_stepObservable_intervalIntegrable {α : Type*} (height gain : α → ℝ)
    (base v : ℝ) (events : List α) (a b : ℝ) :
    IntervalIntegrable (fun y => Real.exp (v*y)*stepObservable height gain base events y) volume a b := by
  induction events with
  | nil => exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul_const base).intervalIntegrable a b
  | cons e es ih =>
    have heq : (fun y => Real.exp (v*y)*stepObservable height gain base (e::es) y) =
        fun y => Real.exp (v*y)*stepObservable height gain base es y-
          gain e*(if y < height e then Real.exp (v*y) else 0) := by
      funext y
      by_cases hy : y < height e <;> simp only [stepObservable,hy,↓reduceIte] <;> ring
    rw [heq]
    exact ih.sub ((exponential_step_intervalIntegrable v (height e) a b).const_mul (gain e))

private theorem jump_boundary_identity (v a b h g : ℝ) (hab : a ≤ b) :
    (if a < h ∧ h ≤ b then Real.exp (v*h)*g else 0) =
      -Real.exp (v*b)*(if b < h then g else 0)+Real.exp (v*a)*(if a < h then g else 0)+
        g*(Real.exp (v*min b h)-Real.exp (v*min a h)) := by
  by_cases hha : h ≤ a
  · simp only [not_lt_of_ge hha,not_lt_of_ge (hha.trans hab),false_and,↓reduceIte,
      min_eq_right (hha.trans hab),min_eq_right hha]
    ring
  · have hah : a < h := lt_of_not_ge hha
    by_cases hbh : b < h
    · simp only [hah,hbh,not_le_of_gt hbh,and_false,↓reduceIte,min_eq_left hbh.le,min_eq_left hah.le]
      ring
    · have hhb : h ≤ b := le_of_not_gt hbh
      simp only [hah,hbh,hhb,not_false_eq_true,and_self,↓reduceIte,min_eq_right hhb,min_eq_left hah.le]
      ring

/-- Finite integration by parts, with ties counted with multiplicity.
It holds for arbitrary signed jump coefficients and either endpoint
convention is handled exactly. -/
theorem finite_weighted_jump_identity {α : Type*} (height gain : α → ℝ) (base v a b : ℝ)
    (events : List α) (hab : a ≤ b) :
    (events.map fun e => if a < height e ∧ height e ≤ b then Real.exp (v*height e)*gain e else 0).sum =
      Real.exp (v*b)*stepObservable height gain base events b-
        Real.exp (v*a)*stepObservable height gain base events a-
        v*(∫ y in a..b, Real.exp (v*y)*stepObservable height gain base events y) := by
  induction events with
  | nil =>
    simp only [List.map_nil,List.sum_nil,stepObservable,intervalIntegral.integral_mul_const]
    have hi := scaled_exponential_integral v a b
    linear_combination base*hi
  | cons e es ih =>
    have heq : (fun y => Real.exp (v*y)*stepObservable height gain base (e::es) y) =
        fun y => Real.exp (v*y)*stepObservable height gain base es y-
          gain e*(if y < height e then Real.exp (v*y) else 0) := by
      funext y
      by_cases hy : y < height e <;> simp only [stepObservable,hy,↓reduceIte] <;> ring
    rw [heq,intervalIntegral.integral_sub (weighted_stepObservable_intervalIntegrable height gain base v es a b)
      ((exponential_step_intervalIntegrable v (height e) a b).const_mul (gain e)),intervalIntegral.integral_const_mul]
    simp only [List.map_cons,List.sum_cons,stepObservable]
    have hs := exponential_step_integral v a b (height e) hab
    have hbnd := jump_boundary_identity v a b (height e) (gain e) hab
    linear_combination ih+hbnd-gain e*hs

/-- The unweighted power changes telescope over precisely the same
height window as the logarithmic jump identity. -/
theorem finite_jump_difference {α : Type*} (height gain : α → ℝ) (base a b : ℝ)
    (events : List α) (hab : a ≤ b) :
    stepObservable height gain base events b-stepObservable height gain base events a =
      (events.map fun e => if a < height e ∧ height e ≤ b then gain e else 0).sum := by
  induction events with
  | nil => simp [stepObservable]
  | cons e es ih =>
    simp only [stepObservable,List.map_cons,List.sum_cons]
    by_cases hha : height e ≤ a
    · simp only [not_lt_of_ge hha,not_lt_of_ge (hha.trans hab),false_and,↓reduceIte]
      linarith only [ih]
    · have hah := lt_of_not_ge hha
      by_cases hbh : b < height e
      · simp only [hah,hbh,not_le_of_gt hbh,and_false,↓reduceIte]
        linarith only [ih]
      · simp only [hah,hbh,le_of_not_gt hbh,and_self,↓reduceIte]
        linarith only [ih]

end
end StrongSilver
