-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.GoodDepthEnvelope
import StrongSilver.IndexedBalancedEdgeSpacing

namespace StrongSilver
open Real Set MeasureTheory ScheduleTree BinaryForest
noncomputable section
set_option maxHeartbeats 5600000

/-- Each selected pivot contributes on a one-sided interval of
cutoffs. Its weighted integral is paid by its original vertex weight. -/
theorem selected_node_integrable (φ : ℝ → ℝ) (P v a b : ℝ) (q : ScheduleNode) (c : ℝ) :
    IntervalIntegrable (fun y => if P+Real.exp y < φ q.pivot then Real.exp (v*y)*c else 0) volume a b := by
  by_cases hq : P < φ q.pivot
  · have he : (fun y => if P+Real.exp y < φ q.pivot then Real.exp (v*y)*c else 0) =
        fun y => (if y < nodePaddedHeight φ P q then Real.exp (v*y) else 0)*c := by
      funext y
      have hh : P+Real.exp y < φ q.pivot ↔ y < nodePaddedHeight φ P q := by
        change P+Real.exp y < φ q.pivot ↔ y < Real.log (φ q.pivot-P)
        rw [Real.lt_log_iff_exp_lt (sub_pos.mpr hq)]
        change P+Real.exp y < φ q.pivot ↔ Real.exp y < φ q.pivot-P
        constructor <;> intro h <;> linarith only [h]
      simp only [hh]
      split_ifs <;> simp
    rw [he]
    exact (exponential_step_intervalIntegrable v (nodePaddedHeight φ P q) a b).mul_const c
  · have he : (fun y => if P+Real.exp y < φ q.pivot then Real.exp (v*y)*c else 0) = fun _ => (0:ℝ) := by
      funext y
      apply if_neg
      have hh := le_of_not_gt hq
      have hx := Real.exp_pos y
      linarith only [hh,hx]
    rw [he]
    exact intervalIntegrable_const

theorem selected_node_integral_upper (φ : ℝ → ℝ) (P v a b : ℝ) (q : ScheduleNode) (c : ℝ)
    (hv : 0 ≤ v) (hc : 0 ≤ c) (hab : a ≤ b) :
    v*(∫ y in a..b, if P+Real.exp y < φ q.pivot then Real.exp (v*y)*c else 0) ≤
      Real.exp (v*nodePaddedHeight φ P q)*c := by
  by_cases hq : P < φ q.pivot
  · have he : (fun y => if P+Real.exp y < φ q.pivot then Real.exp (v*y)*c else 0) =
        fun y => (if y < nodePaddedHeight φ P q then Real.exp (v*y) else 0)*c := by
      funext y
      have hh : P+Real.exp y < φ q.pivot ↔ y < nodePaddedHeight φ P q := by
        change P+Real.exp y < φ q.pivot ↔ y < Real.log (φ q.pivot-P)
        rw [Real.lt_log_iff_exp_lt (sub_pos.mpr hq)]
        change P+Real.exp y < φ q.pivot ↔ Real.exp y < φ q.pivot-P
        constructor <;> intro h <;> linarith only [h]
      simp only [hh]
      split_ifs <;> simp
    rw [he,intervalIntegral.integral_mul_const]
    have hi := exponential_step_scaled_upper v (nodePaddedHeight φ P q) a b hv hab
    have hh := mul_le_mul_of_nonneg_right hi hc
    linear_combination hh
  · have he : (fun y => if P+Real.exp y < φ q.pivot then Real.exp (v*y)*c else 0) = fun _ => (0:ℝ) := by
      funext y
      apply if_neg
      have hh := le_of_not_gt hq
      have hx := Real.exp_pos y
      linarith only [hh,hx]
    rw [he,intervalIntegral.integral_zero,mul_zero]
    exact mul_nonneg (Real.exp_pos _).le hc

def selectedNodeObservable (φ : ℝ → ℝ) (P v : ℝ) (F : ScheduleNode → ℝ) (xs : List ScheduleNode) (y : ℝ) : ℝ :=
  (xs.map fun q => if P+Real.exp y < φ q.pivot then Real.exp (v*y)*F q else 0).sum

theorem selectedNodeObservable_integrable (φ : ℝ → ℝ) (P v a b : ℝ) (F : ScheduleNode → ℝ) (xs : List ScheduleNode) :
    IntervalIntegrable (selectedNodeObservable φ P v F xs) volume a b := by
  induction xs with
  | nil => exact intervalIntegrable_const
  | cons q qs ih => exact (selected_node_integrable φ P v a b q (F q)).add ih

theorem selectedNodeObservable_integral_upper (φ : ℝ → ℝ) (P v a b : ℝ) (F : ScheduleNode → ℝ) (xs : List ScheduleNode)
    (hv : 0 ≤ v) (hF : ∀ q, 0 ≤ F q) (hab : a ≤ b) :
    v*(∫ y in a..b, selectedNodeObservable φ P v F xs y) ≤
      (xs.map fun q => Real.exp (v*nodePaddedHeight φ P q)*F q).sum := by
  induction xs with
  | nil => simp [selectedNodeObservable]
  | cons q qs ih =>
    have hq := selected_node_integral_upper φ P v a b q (F q) hv (hF q) hab
    have he : (fun y => selectedNodeObservable φ P v F (q::qs) y) = fun y =>
        (if P+Real.exp y < φ q.pivot then Real.exp (v*y)*F q else 0)+selectedNodeObservable φ P v F qs y := rfl
    rw [he,intervalIntegral.integral_add (selected_node_integrable φ P v a b q (F q))
      (selectedNodeObservable_integrable φ P v a b F qs)]
    simp only [List.map_cons,List.sum_cons]
    linear_combination hq+ih

end
end StrongSilver
