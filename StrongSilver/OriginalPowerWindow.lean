-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CartesianPowerWindow
import StrongSilver.OriginalNodeExcessSum

namespace StrongSilver.ScheduleTree
noncomputable section
set_option maxHeartbeats 3200000

/-- Exact conversion of the transformed power jumps to the original
signed-tree occurrence list. -/
theorem heightWindowDecrease_eq_transformed {φ : ℝ → ℝ} (hzero : φ 0 = 0)
    (P κ a b : ℝ) (t : ScheduleTree) :
    ((nodesInHeightWindow φ P κ a b t).map fun q => paddedRootDecrease φ P q.2 q.1).sum =
      (((t.mapSteps φ).paddedEvents P κ).map fun q =>
        if a < paddedHeight P q ∧ paddedHeight P q ≤ b then paddedRootDecrease id P q.2 q.1 else 0).sum := by
  rw [paddedEvents_mapSteps hzero,List.map_map]
  have hdec (q : ScheduleTree × ℝ) : paddedRootDecrease id P (mapReservedNode φ q).2 (mapReservedNode φ q).1 = paddedRootDecrease φ P q.2 q.1 :=
    paddedRootDecrease_mapSteps φ P q.2 q.1
  simp only [Function.comp_def,paddedHeight_mapReservedNode hzero,hdec]
  unfold nodesInHeightWindow
  generalize positivePaddedNodes φ P κ t = qs
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    by_cases hq : a < nodeHeight φ P q ∧ nodeHeight φ P q ≤ b
    · simp only [List.filter_cons,decide_eq_true hq,↓reduceIte,List.map_cons,List.sum_cons,if_pos hq,ih]
    · simp only [List.filter_cons,decide_eq_false hq,Bool.false_eq_true,↓reduceIte,List.map_cons,List.sum_cons,if_neg hq,zero_add,ih]

/-- Window telescoping for the actual original word. A transformed
Cartesian tree is required and is constructed explicitly in applications. -/
theorem original_power_window_difference {φ : ℝ → ℝ} (hzero : φ 0 = 0) {P κ : ℝ} (hP : 0 < P)
    (t : ScheduleTree) (hc : (t.mapSteps φ).Cartesian) (a b : ℝ) (hab : a ≤ b) :
    ((nodesInHeightWindow φ P κ a b t).map fun q => paddedRootDecrease φ P q.2 q.1).sum =
      cutPower φ P κ (heightCut φ P b t.word)-cutPower φ P κ (heightCut φ P a t.word) := by
  rw [heightWindowDecrease_eq_transformed hzero]
  rw [cartesian_power_window_difference hP _ hc a b hab]
  rw [transformed_height_cut_power,transformed_height_cut_power]

end
end StrongSilver.ScheduleTree
