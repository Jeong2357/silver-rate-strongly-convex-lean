-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.SmoothedThresholdIntegral
import StrongSilver.FiniteListIntegral
import StrongSilver.FiniteJumpIntegral
import Mathlib.Algebra.BigOperators.Ring.List

namespace StrongSilver
open Real Set MeasureTheory
noncomputable section
set_option maxHeartbeats 6200000
variable {α : Type*}

theorem list_sum_map_sub (f g : α → ℝ) (xs : List α) :
    (xs.map fun x => f x-g x).sum = (xs.map f).sum-(xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons,List.sum_cons,ih]; ring


theorem stepObservable_eq_base_sub_sum (height gain : α → ℝ) (base y : ℝ) (xs : List α) :
    stepObservable height gain base xs y = base-(xs.map fun x => if y < height x then gain x else 0).sum := by
  induction xs with
  | nil => simp [stepObservable]
  | cons x xs ih => simp only [stepObservable,List.map_cons,List.sum_cons,ih]; ring

/-- Exact finite averaging of the threshold-step observable. This
retains all jump occurrences, including coincident heights. -/
theorem smoothed_stepObservable_difference (height gain : α → ℝ) (base u v : ℝ) (xs : List α)
    (hu : 0 < u) (hv : 0 < v) :
    (∫ t in (0:ℝ)..1, (stepObservable height gain base xs (u+t*Real.sqrt u)-
      stepObservable height gain base xs (v+t*Real.sqrt v))) =
    (xs.map fun x => smoothedBandWeight u v (height x)*gain x).sum := by
  let F := fun x : α => fun t : ℝ =>
    ((if v+t*Real.sqrt v < height x then (1:ℝ) else 0)-(if u+t*Real.sqrt u < height x then (1:ℝ) else 0))*gain x
  have hF (x : α) : IntervalIntegrable (F x) volume 0 1 :=
    ((smoothedThresholdIndicator_integrable hv (height x) 0 1).sub (smoothedThresholdIndicator_integrable hu (height x) 0 1)).mul_const (gain x)
  have hEq : (fun t : ℝ => stepObservable height gain base xs (u+t*Real.sqrt u)-
      stepObservable height gain base xs (v+t*Real.sqrt v)) = fun t => (xs.map fun x => F x t).sum := by
    funext t
    rw [stepObservable_eq_base_sub_sum,stepObservable_eq_base_sub_sum]
    dsimp only [F]
    have hU : (xs.map fun x => (if u+t*Real.sqrt u < height x then (1:ℝ) else 0)*gain x).sum =
        (xs.map fun x => if u+t*Real.sqrt u < height x then gain x else 0).sum := by
      congr 1
      apply List.map_congr_left
      intro x hx
      split_ifs <;> ring
    have hV : (xs.map fun x => (if v+t*Real.sqrt v < height x then (1:ℝ) else 0)*gain x).sum =
        (xs.map fun x => if v+t*Real.sqrt v < height x then gain x else 0).sum := by
      congr 1
      apply List.map_congr_left
      intro x hx
      split_ifs <;> ring
    simp_rw [sub_mul]
    rw [list_sum_map_sub,hU,hV]
    ring
  rw [hEq,integral_list_sum F xs 0 1 (fun x _ => hF x)]
  congr 1
  apply List.map_congr_left
  intro x hx
  dsimp only [F]
  rw [intervalIntegral.integral_mul_const,← smoothedBandWeight_integral hu hv (height x)]

end
end StrongSilver
