-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ScheduleCut
import Mathlib.Data.List.Range
import Mathlib.Data.List.Nodup

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 3600000

/-- Selected cut phases keep distinct original indices. -/
theorem cutScheduleFrom_phase_indices_nodup (choose : ℕ → ℝ → Bool) (start : ℕ) (h : List ℝ) :
    (((cutScheduleFrom choose start h).phases).map CutPhase.index).Nodup := by
  let xs := (h.zipIdx start).map Prod.swap
  have hAll : (xs.map Prod.fst).Nodup := by
    dsimp only [xs]
    simp only [List.map_map,Function.comp_def,Prod.fst_swap]
    rw [List.zipIdx_map_snd]
    exact List.nodup_range'
  have hSub : ((xs.filter (fun p => choose p.1 p.2)).map Prod.fst).Sublist (xs.map Prod.fst) := List.filter_sublist.map Prod.fst
  have hEq : ((cutScheduleFrom choose start h).phases.map CutPhase.index) =
      ((cutScheduleFrom choose start h).selected.map Prod.fst) := by
    simp only [ScheduleCut.selected,List.map_map,Function.comp_def]
  rw [hEq,cutScheduleFrom_selected]
  exact hAll.sublist hSub

theorem cutScheduleFrom_phases_nodup (choose : ℕ → ℝ → Bool) (start : ℕ) (h : List ℝ) :
    (cutScheduleFrom choose start h).phases.Nodup :=
  List.Nodup.of_map CutPhase.index (cutScheduleFrom_phase_indices_nodup choose start h)

end
end StrongSilver
