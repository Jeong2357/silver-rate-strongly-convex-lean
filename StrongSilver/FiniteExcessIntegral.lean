-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FiniteJumpIntegral

namespace StrongSilver
open Real MeasureTheory
noncomputable section
set_option maxHeartbeats 3000000

theorem stepObservable_sub_base {α : Type*} (height gain : α → ℝ) (base center : ℝ) (events : List α) (y : ℝ) :
    stepObservable height gain (base-center) events y = stepObservable height gain base events y-center := by
  induction events with
  | nil => rfl
  | cons e es ih => simp only [stepObservable,ih]; ring

/-- Exact finite integration-by-parts identity for excesses. The two
observables use the same original event list and height window. -/
theorem finite_excess_integral_identity {α : Type*} (height gain decrease : α → ℝ)
    (logBase powerBase center c v a b : ℝ) (events : List α) (hab : a ≤ b) :
    (events.map fun e => if a < height e ∧ height e ≤ b then
      c*Real.exp (v*height e)*gain e-decrease e else 0).sum+
      c*v*(∫ y in a..b, Real.exp (v*y)*(stepObservable height gain logBase events y-center)) =
    c*(Real.exp (v*b)*(stepObservable height gain logBase events b-center)-
      Real.exp (v*a)*(stepObservable height gain logBase events a-center))+
      stepObservable height decrease powerBase events a-stepObservable height decrease powerBase events b := by
  have hlog := finite_weighted_jump_identity height gain (logBase-center) v a b events hab
  simp only [stepObservable_sub_base] at hlog
  have hpower := finite_jump_difference height decrease powerBase a b events hab
  have hsum : (events.map fun e => if a < height e ∧ height e ≤ b then
      c*Real.exp (v*height e)*gain e-decrease e else 0).sum =
      c*(events.map fun e => if a < height e ∧ height e ≤ b then Real.exp (v*height e)*gain e else 0).sum-
        (events.map fun e => if a < height e ∧ height e ≤ b then decrease e else 0).sum := by
    clear hlog hpower
    induction events with
    | nil => simp
    | cons e es ih =>
      simp only [List.map_cons,List.sum_cons]
      by_cases he : a < height e ∧ height e ≤ b
      · simp only [if_pos he,ih]
        ring
      · simp only [if_neg he,ih]
        ring
  rw [hsum]
  linear_combination c*hlog+hpower

end
end StrongSilver
