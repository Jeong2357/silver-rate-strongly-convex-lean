-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CutGapRefinements

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 2800000

theorem ScheduleCut.unselected_concat_selected (C D : ScheduleCut) (j : ℕ) (b : ℝ) :
    (C.concat (D.prependSelected j b)).unselected = C.unselected++D.unselected := by
  unfold ScheduleCut.unselected
  rw [ScheduleCut.gaps_concat_selected,List.flatten_append]

theorem refineCutGaps_selected_property (Q : ℕ → ℝ → Prop)
    (choose : CutPhase → ℕ → ℝ → Bool) (D : ScheduleCut) (qs : List CutPhase)
    (hold : ∀ q ∈ qs, Q q.index q.pivot)
    (hchoose : ∀ q ∈ qs, ∀ j b, choose q j b = true → Q j b)
    (hD : ∀ q ∈ D.phases, Q q.index q.pivot) :
    ∀ q ∈ (refineCutGaps choose D qs).phases, Q q.index q.pivot := by
  induction qs with
  | nil => exact hD
  | cons q qs ih =>
    intro p hp
    simp only [refineCutGaps,ScheduleCut.concat_before_selected,List.mem_append,List.mem_cons] at hp
    rcases hp with hp | rfl | hp
    · exact hchoose q (by simp) p.index p.pivot (cutScheduleFrom_selected_property hp)
    · exact hold q (by simp)
    · exact ih (fun p hp => hold p (List.mem_cons_of_mem q hp))
        (fun p hp => hchoose p (List.mem_cons_of_mem q hp)) p hp

theorem refineCutGaps_unselected_property (Q : ℝ → Prop)
    (choose : CutPhase → ℕ → ℝ → Bool) (D : ScheduleCut) (qs : List CutPhase)
    (hgap : ∀ q ∈ qs, ∀ b ∈ q.gap, Q b)
    (hD : ∀ b ∈ D.unselected, Q b) : ∀ b ∈ (refineCutGaps choose D qs).unselected, Q b := by
  induction qs with
  | nil => exact hD
  | cons q qs ih =>
    intro b hb
    rw [refineCutGaps,ScheduleCut.unselected_concat_selected] at hb
    rcases List.mem_append.mp hb with hb | hb
    · exact hgap q (by simp) b ((cutScheduleFrom_unselected_sublist (choose q) _ q.gap).subset hb)
    · exact ih (fun p hp => hgap p (List.mem_cons_of_mem q hp)) b hb

end
end StrongSilver
