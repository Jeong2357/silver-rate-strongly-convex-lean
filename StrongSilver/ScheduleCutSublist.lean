-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ScheduleCutPartition
import StrongSilver.LogConsequences

namespace StrongSilver
noncomputable section

theorem cutScheduleFrom_unselected_sublist (choose : ℕ → ℝ → Bool) (i : ℕ) (h : List ℝ) :
    (cutScheduleFrom choose i h).unselected.Sublist h := by
  induction h generalizing i with
  | nil => exact List.Sublist.slnil
  | cons a h ih =>
    simp only [cutScheduleFrom]
    split
    · rw [ScheduleCut.unselected_prependSelected]
      exact (ih (i+1)).cons a
    · rw [ScheduleCut.unselected_prependUnselected]
      exact (ih (i+1)).cons_cons a

theorem ScheduleCut.gap_sublist_unselected {C : ScheduleCut} {q : CutPhase} (hq : q ∈ C.phases) :
    q.gap.Sublist C.unselected := by
  apply List.sublist_flatten_of_mem
  exact List.mem_append_left _ (List.mem_map.mpr ⟨q,hq,rfl⟩)

theorem ScheduleCut.terminal_sublist_unselected (C : ScheduleCut) : C.terminal.Sublist C.unselected := by
  apply List.sublist_flatten_of_mem
  exact List.mem_append_right _ (by simp)

theorem cutScheduleFrom_gap_sublist {choose : ℕ → ℝ → Bool} {i : ℕ} {h : List ℝ} {q : CutPhase}
    (hq : q ∈ (cutScheduleFrom choose i h).phases) : q.gap.Sublist h :=
  (ScheduleCut.gap_sublist_unselected hq).trans (cutScheduleFrom_unselected_sublist choose i h)

theorem cutScheduleFrom_terminal_sublist (choose : ℕ → ℝ → Bool) (i : ℕ) (h : List ℝ) :
    (cutScheduleFrom choose i h).terminal.Sublist h :=
  (ScheduleCut.terminal_sublist_unselected _).trans (cutScheduleFrom_unselected_sublist choose i h)

theorem list_weight_sublist_le {α : Type*} (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) {l h : List α}
    (hl : l.Sublist h) : (l.map w).sum ≤ (h.map w).sum := by
  induction hl with
  | slnil => exact le_rfl
  | cons a hl ih =>
    simp only [List.map_cons,List.sum_cons]
    linarith only [ih,hw a]
  | cons_cons a hl ih =>
    simp only [List.map_cons,List.sum_cons]
    exact add_le_add le_rfl ih

theorem positiveMass_sublist_le {l h : List ℝ} (hl : l.Sublist h) :
    Scalar.SignedIntervals.positiveMass l ≤ Scalar.SignedIntervals.positiveMass h :=
  list_weight_sublist_le (fun a => max a 0) (fun a => le_max_right a 0) hl

theorem negativeLogSum_sublist_le {T : ℝ} (hT : 0 < T) {l h : List ℝ} (hl : l.Sublist h) :
    negativeLogSum l T ≤ negativeLogSum h T := by
  apply list_weight_sublist_le _ ?_ hl
  intro a
  split_ifs
  · exact Real.log_nonneg (by have hh := div_nonneg (abs_nonneg a) hT.le; linarith only [hh])
  · exact le_rfl

end
end StrongSilver
