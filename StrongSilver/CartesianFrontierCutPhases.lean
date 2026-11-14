-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CartesianFollowingSplit

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 3000000

/-- Keep the terminal gap and its external boundary in the same list
as the actual nonterminal cut phases; the external update is not added
to the original cut word. -/
def cutPhasePairs (b : ℝ) (C : ScheduleCut) : List (List ℝ × ℝ) :=
  C.phases.map (fun q => (q.gap,q.pivot))++[(C.terminal,b)]

namespace ScheduleTree

/-- Exact equality between adaptive Cartesian phases and the original
full-cut phases, preserving every gap, following selected step and the
terminal gap. It is stronger than equality of just the gap list. -/
theorem threshold_cut_phases (t : ScheduleTree) (hc : t.Cartesian) {A : ℝ} (hA : 0 ≤ A)
    (i : ℕ) (b : ℝ) :
    cutPhasePairs b (cutScheduleFrom (fun _ p => decide (A < p)) i t.word) =
      (frontierPhases A t b).map (fun q => (q.1.word,q.2)) := by
  induction t generalizing i b with
  | leaf h =>
    have hn : ∀ p ∈ h, ∀ j : ℕ, decide (A < p) = false := by
      intro p hp j
      exact decide_eq_false (not_lt_of_ge ((hc p hp).trans hA))
    rw [word,cutScheduleFrom_none _ i h hn]
    rfl
  | split l p r il ir =>
    by_cases hp : A < p
    · have hsel : decide (A < p) = true := decide_eq_true hp
      rw [word,cutScheduleFrom_append]
      simp only [cutScheduleFrom,hsel,↓reduceIte,ScheduleCut.concat_before_selected]
      have hh := congrArg₂ (fun ps qs : List (List ℝ × ℝ) => ps++qs)
        (il hc.1 i p) (ir hc.2.1 (i+l.word.length+1) b)
      simpa only [cutPhasePairs,List.map_append,List.map_cons,frontierPhases,if_pos hp,
        List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using hh
    · have hall (x : ℝ) (hx : x ∈ (ScheduleTree.split l p r).word) : x ≤ A :=
        (split_word_le hc x hx).trans (le_of_not_gt hp)
      have hn : ∀ x ∈ (ScheduleTree.split l p r).word, ∀ j : ℕ, decide (A < x) = false := by
        intro x hx j
        exact decide_eq_false (not_lt_of_ge (hall x hx))
      rw [cutScheduleFrom_none _ i _ hn]
      simp only [cutPhasePairs,frontierPhases,if_neg hp,List.map_cons,List.map_nil,List.nil_append]

theorem fullCut_phases_from_cartesian (h : List ℝ) {A : ℝ} (hA : 0 ≤ A) (b : ℝ) :
    cutPhasePairs b (fullCut A h) = ((cartesian h).frontierPhases A b).map (fun q => (q.1.word,q.2)) := by
  have hh := threshold_cut_phases (cartesian h) (cartesian_valid h) hA 0 b
  simpa only [cartesian_word,fullCut,cutSchedule] using hh

end ScheduleTree
end
end StrongSilver
