-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ReservedNodeTransform
import StrongSilver.BandIntegralEstimates

namespace StrongSilver.ScheduleTree
noncomputable section
set_option maxHeartbeats 3200000

def nodesInHeightWindow (φ : ℝ → ℝ) (P κ a b : ℝ) (t : ScheduleTree) : List (ScheduleTree × ℝ) :=
  (positivePaddedNodes φ P κ t).filter (fun q => decide (a < nodeHeight φ P q ∧ nodeHeight φ P q ≤ b))

/-- The event list used in the actual excess integral is exactly the
original signed-tree occurrence list with transformed heights. -/
theorem heightWindowExcess_eq_transformed {φ : ℝ → ℝ} (hzero : φ 0 = 0)
    (P κ a b : ℝ) (t : ScheduleTree) :
    ((nodesInHeightWindow φ P κ a b t).map (nodeExcess φ P)).sum =
      (((t.mapSteps φ).paddedEvents P κ).map fun q =>
        if a < paddedHeight P q ∧ paddedHeight P q ≤ b then paddedEventExcess P q else 0).sum := by
  rw [paddedEvents_mapSteps hzero,List.map_map]
  simp only [Function.comp_def,paddedHeight_mapReservedNode hzero,paddedExcess_mapReservedNode hzero]
  unfold nodesInHeightWindow
  generalize positivePaddedNodes φ P κ t = qs
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    by_cases hq : a < nodeHeight φ P q ∧ nodeHeight φ P q ≤ b
    · simp only [List.filter_cons,decide_eq_true hq,↓reduceIte,List.map_cons,List.sum_cons,if_pos hq,ih]
    · simp only [List.filter_cons,decide_eq_false hq,Bool.false_eq_true,↓reduceIte,List.map_cons,List.sum_cons,if_neg hq,zero_add,ih]

theorem nodesInHeightWindow_root_positive {φ : ℝ → ℝ} {P κ a b : ℝ} {t : ScheduleTree} {q : ScheduleTree × ℝ}
    (hq : q ∈ nodesInHeightWindow φ P κ a b t) : P < φ q.1.rootStep :=
  of_decide_eq_true (List.mem_filter.mp (List.mem_filter.mp hq).1).2

theorem nodesInHeightWindow_reserve_nonnegative {φ : ℝ → ℝ} {P κ a b : ℝ} {t : ScheduleTree} {q : ScheduleTree × ℝ}
    (hκ : 0 ≤ κ) (hq : q ∈ nodesInHeightWindow φ P κ a b t) : 0 ≤ q.2 :=
  reservedNodes_reserve_nonnegative hκ (List.mem_filter.mp (List.mem_filter.mp hq).1).1

end
end StrongSilver.ScheduleTree
