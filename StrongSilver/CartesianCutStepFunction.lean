-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ReservedTreeNodes
import StrongSilver.FiniteJumpIntegral

namespace StrongSilver.ScheduleTree
noncomputable section
set_option maxHeartbeats 3200000

/-- All splits whose transformed selected factor is positive. -/
def paddedEvents (P κ : ℝ) (t : ScheduleTree) : List (ScheduleTree × ℝ) :=
  (t.reservedNodes κ).filter (fun q => decide (P < q.1.rootStep))

def paddedHeight (P : ℝ) (q : ScheduleTree × ℝ) : ℝ := Real.log (q.1.rootStep-P)

private theorem node_sum_to_height (P y κ : ℝ) (F : ℝ → ScheduleTree → ℝ) (t : ScheduleTree) :
    ((t.reservedNodes κ).map fun q => if P+Real.exp y < q.1.rootStep then F q.2 q.1 else 0).sum =
      ((t.paddedEvents P κ).map fun q => if y < paddedHeight P q then F q.2 q.1 else 0).sum := by
  unfold paddedEvents
  generalize t.reservedNodes κ = qs
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    by_cases hq : P < q.1.rootStep
    · have hiff : P+Real.exp y < q.1.rootStep ↔ y < paddedHeight P q := by
        rw [paddedHeight,Real.lt_log_iff_exp_lt (sub_pos.mpr hq)]
        constructor <;> intro h <;> linarith only [h]
      simp only [List.filter_cons,decide_eq_true hq,↓reduceIte,List.map_cons,List.sum_cons,ih,hiff]
    · have hnone : ¬ P+Real.exp y < q.1.rootStep := by
        have he := Real.exp_pos y
        linarith only [le_of_not_gt hq,he]
      simp only [List.filter_cons,decide_eq_false hq,Bool.false_eq_true,↓reduceIte,List.map_cons,List.sum_cons,if_neg hnone,zero_add,ih]

theorem stepObservable_eq_base_sub_sum {α : Type*} (height gain : α → ℝ) (base : ℝ) (events : List α) (y : ℝ) :
    stepObservable height gain base events y = base-(events.map fun e => if y < height e then gain e else 0).sum := by
  induction events with
  | nil => simp [stepObservable]
  | cons e es ih => simp only [stepObservable,ih,List.map_cons,List.sum_cons]; ring

/-- The full-cut logarithm is an exact finite step observable in the
height y=log(A-P), with no endpoint exclusions or generic-position premise. -/
theorem full_cut_log_stepObservable {P κ : ℝ} (hP : 0 < P) (hκ : 0 ≤ κ)
    (t : ScheduleTree) (hc : t.Cartesian) (y : ℝ) :
    cutLogProduct id P κ (fullCut (P+Real.exp y) t.word) =
      stepObservable (paddedHeight P) (fun q => paddedRootGain id P q.2 q.1)
        (Real.log (gapPrefix id t.word+P+κ)) (t.paddedEvents P κ) y := by
  have hA : 0 ≤ P+Real.exp y := add_nonneg hP.le (Real.exp_pos y).le
  have hφ : ∀ b ∈ t.word, P+Real.exp y < b → P < id b := by
    intro b hb h
    have he := Real.exp_pos y
    change P < b
    linarith only [h,he]
  have hh := full_cut_log_jump_formula hP hκ hA t hc hφ 0
  rw [splitSumAbove_eq_node_sum _ _ _ t hc,node_sum_to_height] at hh
  rw [stepObservable_eq_base_sub_sum]
  exact hh

theorem full_cut_power_stepObservable {P κ : ℝ} (hP : 0 < P) (t : ScheduleTree) (hc : t.Cartesian) (y : ℝ) :
    cutPower id P κ (fullCut (P+Real.exp y) t.word) =
      stepObservable (paddedHeight P) (fun q => paddedRootDecrease id P q.2 q.1)
        ((gapPrefix id t.word+P+κ)^nu) (t.paddedEvents P κ) y := by
  have hA : 0 ≤ P+Real.exp y := add_nonneg hP.le (Real.exp_pos y).le
  have hh := full_cut_power_jump_formula (φ := id) (P := P) (κ := κ) hA t hc 0
  rw [splitSumAbove_eq_node_sum _ _ _ t hc,node_sum_to_height] at hh
  rw [stepObservable_eq_base_sub_sum]
  exact hh

end
end StrongSilver.ScheduleTree
