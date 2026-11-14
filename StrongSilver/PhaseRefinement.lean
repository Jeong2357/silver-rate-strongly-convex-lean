-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ScheduleCutSublist

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 1400000

def refinePhase (choose : ℕ → ℝ → Bool) (q : CutPhase) : List CutPhase :=
  let C := cutScheduleFrom choose (q.index-q.gap.length) q.gap
  C.phases ++ [⟨C.terminal,q.pivot,q.index⟩]

theorem refinePhase_word (choose : ℕ → ℝ → Bool) (q : CutPhase) :
    (refinePhase choose q).flatMap CutPhase.word = q.word := by
  let C := cutScheduleFrom choose (q.index-q.gap.length) q.gap
  have hword : C.phases.flatMap CutPhase.word++C.terminal = q.gap := cutScheduleFrom_word choose _ _
  change (C.phases++[(⟨C.terminal,q.pivot,q.index⟩ : CutPhase)]).flatMap CutPhase.word = q.word
  simp only [List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,CutPhase.word]
  rw [← List.append_assoc,hword]

theorem refinePhase_nonempty (choose : ℕ → ℝ → Bool) (q : CutPhase) : refinePhase choose q ≠ [] := by
  simp [refinePhase]

theorem refinePhase_gap_sublist {choose : ℕ → ℝ → Bool} {q z : CutPhase}
    (hz : z ∈ refinePhase choose q) : z.gap.Sublist q.gap := by
  simp only [refinePhase,List.mem_append,List.mem_singleton] at hz
  rcases hz with hz | rfl
  · exact cutScheduleFrom_gap_sublist hz
  · exact cutScheduleFrom_terminal_sublist choose _ _

theorem refinePhase_pivot_mem {choose : ℕ → ℝ → Bool} {q z : CutPhase}
    (hz : z ∈ refinePhase choose q) : z.pivot ∈ q.gap ∨ z.pivot = q.pivot := by
  simp only [refinePhase,List.mem_append,List.mem_singleton] at hz
  rcases hz with hz | rfl
  · have hh := ScheduleCut.mem_word_of_mem_pivot hz
    rw [cutScheduleFrom_word] at hh
    exact Or.inl hh
  · exact Or.inr rfl

theorem refinePhase_pivot_lower {choose : ℕ → ℝ → Bool} {A : ℝ} {q z : CutPhase}
    (hc : ∀ i a, choose i a = true → A ≤ a) (hq : A ≤ q.pivot) (hz : z ∈ refinePhase choose q) : A ≤ z.pivot := by
  simp only [refinePhase,List.mem_append,List.mem_singleton] at hz
  rcases hz with hz | rfl
  · exact hc _ _ (cutScheduleFrom_selected_property hz)
  · exact hq

theorem refinePhase_gap_cap {choose : ℕ → ℝ → Bool} {A : ℝ} {q z : CutPhase}
    (hc : ∀ i a, choose i a = false → 0 < a → a ≤ A) (hz : z ∈ refinePhase choose q) :
    ∀ b ∈ z.gap, 0 < b → b ≤ A := by
  simp only [refinePhase,List.mem_append,List.mem_singleton] at hz
  rcases hz with hz | rfl
  · intro b hb hb0
    have hh := ScheduleCut.mem_gap_unselected hz hb
    exact cutScheduleFrom_unselected_property (fun a => 0 < a → a ≤ A) hc _ _ b hh hb0
  · intro b hb hb0
    have hh := ScheduleCut.mem_terminal_unselected hb
    exact cutScheduleFrom_unselected_property (fun a => 0 < a → a ≤ A) hc _ _ b hh hb0

theorem refinePhase_positiveMass_le {choose : ℕ → ℝ → Bool} {q z : CutPhase} (hz : z ∈ refinePhase choose q) :
    Scalar.SignedIntervals.positiveMass z.gap ≤ Scalar.SignedIntervals.positiveMass q.gap :=
  positiveMass_sublist_le (refinePhase_gap_sublist hz)

theorem refinePhase_negativeLogSum_le {choose : ℕ → ℝ → Bool} {q z : CutPhase} {κ : ℝ}
    (hκ : 0 < κ) (hz : z ∈ refinePhase choose q) : negativeLogSum z.gap κ ≤ negativeLogSum q.gap κ :=
  negativeLogSum_sublist_le hκ (refinePhase_gap_sublist hz)

end
end StrongSilver
