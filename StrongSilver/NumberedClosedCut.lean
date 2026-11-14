-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.NumberedCutRefinement

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 1800000

theorem cutScheduleFrom_none (choose : ℕ → ℝ → Bool) (i : ℕ) (h : List ℝ)
    (hh : ∀ b ∈ h, ∀ j : ℕ, choose j b = false) : cutScheduleFrom choose i h = ⟨[],h⟩ := by
  induction h generalizing i with
  | nil => rfl
  | cons b h ih =>
    have hb := hh b (by simp) i
    have ht := ih (i+1) (fun z hz => hh z (List.mem_cons_of_mem b hz))
    simp only [cutScheduleFrom,hb,Bool.false_eq_true,↓reduceIte,ht,ScheduleCut.prependUnselected]

theorem refinePhase_none (choose : ℕ → ℝ → Bool) (q : CutPhase)
    (hh : ∀ b ∈ q.gap, ∀ j : ℕ, choose j b = false) : refinePhase choose q = [q] := by
  have hc := cutScheduleFrom_none choose (q.index-q.gap.length) q.gap hh
  simp only [refinePhase,hc,List.nil_append]

theorem refinePhase_closed_below {B : ℝ} (q : CutPhase) (hh : ∀ b ∈ q.gap, b < B) :
    refinePhase (fun _ b => decide (B ≤ b)) q = [q] := by
  apply refinePhase_none
  intro b hb j
  exact decide_eq_false (not_le.mpr (hh b hb))

theorem numberTrackedPhases_refine_closed {B : ℝ} (i : ℕ) (qs : List CutPhase)
    (hgap : ∀ q ∈ qs, ∀ b ∈ q.gap, b < B) :
    (numberTrackedPhases i qs).flatMap (refinePhase (fun _ b => decide (B ≤ b))) = numberTrackedPhases i qs := by
  induction qs generalizing i with
  | nil => rfl
  | cons q qs ih =>
    have hq := refinePhase_closed_below (q.withIndex (i+q.gap.length)) (hgap q (by simp))
    have ht := ih (i+q.word.length) (fun z hz => hgap z (List.mem_cons_of_mem q hz))
    simp only [numberTrackedPhases,List.flatMap_cons,hq,List.singleton_append,ht]

/-- The compressed tracked schedule starts at exactly its original
tracked phases; numbering supplies its actual chronological positions. -/
theorem closedCut_numbered_phases {B : ℝ} (qs : List CutPhase)
    (hpiv : ∀ q ∈ qs, B ≤ q.pivot) (hgap : ∀ q ∈ qs, ∀ b ∈ q.gap, b < B) :
    closedCut B (qs.flatMap CutPhase.word) = ⟨numberTrackedPhases 0 qs,[]⟩ := by
  have hc := cut_numbered_phases_of_selected_pivots (B := B) (fun _ b => decide (B ≤ b))
    (fun _ _ hb => decide_eq_true hb) 0 qs hpiv
  rw [numberTrackedPhases_refine_closed 0 qs hgap] at hc
  exact hc

end
end StrongSilver
