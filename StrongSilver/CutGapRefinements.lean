-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CartesianPaddedJumps
import StrongSilver.PhaseRefinement

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 3200000

/-- Refine each original nonterminal gap independently; every original
selected pivot is retained as a boundary of its original phase. -/
def refineCutGaps (choose : CutPhase → ℕ → ℝ → Bool) (terminalCut : ScheduleCut) :
    List CutPhase → ScheduleCut
  | [] => terminalCut
  | q::qs => (cutScheduleFrom (choose q) (q.index-q.gap.length) q.gap).concat
      ((refineCutGaps choose terminalCut qs).prependSelected q.index q.pivot)

/-- Original word preservation does not require a good-phase premise. -/
theorem refineCutGaps_word (choose : CutPhase → ℕ → ℝ → Bool) (D : ScheduleCut) (qs : List CutPhase) :
    (refineCutGaps choose D qs).word = qs.flatMap CutPhase.word++D.word := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    simp only [refineCutGaps,ScheduleCut.concat_before_selected,ScheduleCut.word,List.flatMap_append,
      List.flatMap_cons,CutPhase.word,List.append_assoc] at ⊢
    have hc := cutScheduleFrom_word (choose q) (q.index-q.gap.length) q.gap
    simp only [ScheduleCut.word] at hc ih
    rw [← List.append_assoc,← List.append_assoc,hc]
    simpa only [List.append_assoc] using congrArg (fun w => q.gap++[q.pivot]++w) ih

theorem refineCutGaps_count (choose : CutPhase → ℕ → ℝ → Bool) (D : ScheduleCut) (qs : List CutPhase) :
    (refineCutGaps choose D qs).phases.length = qs.length+D.phases.length+
      (qs.map fun q => (cutScheduleFrom (choose q) (q.index-q.gap.length) q.gap).phases.length).sum := by
  induction qs with
  | nil => simp [refineCutGaps]
  | cons q qs ih =>
    simp only [refineCutGaps,ScheduleCut.concat_before_selected,List.length_append,List.length_cons,
      List.map_cons,List.sum_cons,ih]
    omega

/-- Exact logarithmic additivity of the per-gap refinements. The
original selected denominators are charged once and remain unchanged. -/
theorem refineCutGaps_log (φ : ℝ → ℝ) (P κ : ℝ)
    (choose : CutPhase → ℕ → ℝ → Bool) (D : ScheduleCut) (qs : List CutPhase) :
    cutLogProduct φ P κ (refineCutGaps choose D qs) = cutLogProduct φ P κ D+
      (qs.map fun q => cutLogProduct φ P 0 (cutScheduleFrom (choose q) (q.index-q.gap.length) q.gap)-
        Real.log (φ q.pivot-P)).sum := by
  induction qs with
  | nil => simp [refineCutGaps]
  | cons q qs ih =>
    rw [refineCutGaps,cut_log_concat_selected,ih]
    simp only [List.map_cons,List.sum_cons]
    ring

end
end StrongSilver
