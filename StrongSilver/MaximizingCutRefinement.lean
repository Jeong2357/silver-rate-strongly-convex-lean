-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FiniteGapSavings
import StrongSilver.CutGapRefinementProperties

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 3200000

def maximizingPhaseSelector (φ : ℝ → ℝ) (P price : ℝ) (eligible : ℕ → ℝ → Bool) (q : CutPhase) : ℕ → ℝ → Bool :=
  let start := q.index-q.gap.length
  gapMaskSelector start (maximizingGapMask φ P 0 price start q.gap eligible) eligible

def maximizingTerminalCut (φ : ℝ → ℝ) (P κ price : ℝ) (eligible : ℕ → ℝ → Bool) (C : ScheduleCut) : ScheduleCut :=
  let start := C.word.length-C.terminal.length
  cutScheduleFrom (gapMaskSelector start (maximizingGapMask φ P κ price start C.terminal eligible) eligible) start C.terminal

def maximizingCutRefinement (φ : ℝ → ℝ) (P κ price : ℝ) (eligible : ℕ → ℝ → Bool) (C : ScheduleCut) : ScheduleCut :=
  refineCutGaps (maximizingPhaseSelector φ P price eligible) (maximizingTerminalCut φ P κ price eligible C) C.phases

/-- The sum over all original gaps, including the terminal gap. -/
def totalGapSavingsMaximum (φ : ℝ → ℝ) (P κ price : ℝ) (eligible : ℕ → ℝ → Bool) (C : ScheduleCut) : ℝ :=
  (C.phases.map fun q => gapSavingsMaximum φ P 0 price (q.index-q.gap.length) q.gap eligible).sum+
    gapSavingsMaximum φ P κ price (C.word.length-C.terminal.length) C.terminal eligible

theorem maximizingCutRefinement_word (φ : ℝ → ℝ) (P κ price : ℝ) (eligible : ℕ → ℝ → Bool) (C : ScheduleCut) :
    (maximizingCutRefinement φ P κ price eligible C).word = C.word := by
  rw [maximizingCutRefinement,refineCutGaps_word]
  change C.phases.flatMap CutPhase.word++(cutScheduleFrom _ _ C.terminal).word = C.word
  rw [cutScheduleFrom_word]
  rfl

theorem totalGapSavingsMaximum_nonnegative (φ : ℝ → ℝ) (P κ price : ℝ) (eligible : ℕ → ℝ → Bool) (C : ScheduleCut) :
    0 ≤ totalGapSavingsMaximum φ P κ price eligible C := by
  apply add_nonneg
  · apply List.sum_nonneg
    intro x hx
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hx
    exact gapSavingsMaximum_nonnegative _ _ _ _ _ _ _
  · exact gapSavingsMaximum_nonnegative _ _ _ _ _ _ _

theorem maximizingCutRefinement_savings (φ : ℝ → ℝ) (P κ price : ℝ) (eligible : ℕ → ℝ → Bool) (C : ScheduleCut) :
    totalGapSavingsMaximum φ P κ price eligible C =
      cutLogProduct φ P κ C-cutLogProduct φ P κ (maximizingCutRefinement φ P κ price eligible C)-
        price*(((maximizingCutRefinement φ P κ price eligible C).phases.length:ℝ)-(C.phases.length:ℝ)) := by
  exact refinement_savings_identity φ P κ price (maximizingPhaseSelector φ P price eligible)
    (maximizingTerminalCut φ P κ price eligible C) C.phases C.terminal

theorem maximizingCutRefinement_selected_property (φ : ℝ → ℝ) (P κ price : ℝ)
    (eligible : ℕ → ℝ → Bool) (C : ScheduleCut) (Q : ℕ → ℝ → Prop)
    (hold : ∀ q ∈ C.phases, Q q.index q.pivot)
    (heligible : ∀ j b, eligible j b = true → Q j b) :
    ∀ q ∈ (maximizingCutRefinement φ P κ price eligible C).phases, Q q.index q.pivot := by
  apply refineCutGaps_selected_property Q _ _ C.phases hold
  · intro q hq j b hh
    exact heligible j b (gapMaskSelector_eligible hh)
  · intro q hq
    exact heligible q.index q.pivot (gapMaskSelector_eligible (cutScheduleFrom_selected_property hq))

theorem maximizingCutRefinement_unselected_property (φ : ℝ → ℝ) (P κ price : ℝ)
    (eligible : ℕ → ℝ → Bool) (C : ScheduleCut) (Q : ℝ → Prop)
    (hQ : ∀ b ∈ C.unselected, Q b) :
    ∀ b ∈ (maximizingCutRefinement φ P κ price eligible C).unselected, Q b := by
  apply refineCutGaps_unselected_property Q _ _ C.phases
  · intro q hq b hb
    exact hQ b ((C.gap_sublist_unselected hq).subset hb)
  · intro b hb
    have hsub := cutScheduleFrom_unselected_sublist
      (gapMaskSelector (C.word.length-C.terminal.length)
        (maximizingGapMask φ P κ price (C.word.length-C.terminal.length) C.terminal eligible) eligible)
      (C.word.length-C.terminal.length) C.terminal
    exact hQ b (C.terminal_sublist_unselected.subset (hsub.subset hb))

end
end StrongSilver
