-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CanonicalPositionCuts

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 1600000

/-- A finite schedule has an empty value interval immediately below any
fixed cutoff, including when that cutoff has repeated values. -/
theorem exists_empty_threshold_interval (h : List ℝ) {lo B : ℝ} (hlo : lo < B) :
    ∃ A : ℝ, lo ≤ A ∧ A < B ∧ ∀ b ∈ h, b < B → b ≤ A := by
  induction h with
  | nil => exact ⟨lo,le_rfl,hlo,by simp⟩
  | cons b h ih =>
    obtain ⟨A,hloA,hAB,hbound⟩ := ih
    by_cases hb : b < B
    · refine ⟨max b A,hloA.trans (le_max_right _ _),max_lt hb hAB,?_⟩
      intro x hx hxB
      rcases List.mem_cons.mp hx with rfl | hx
      · exact le_max_left _ _
      · exact (hbound x hx hxB).trans (le_max_right _ _)
    · refine ⟨A,hloA,hAB,?_⟩
      intro x hx hxB
      rcases List.mem_cons.mp hx with rfl | hx
      · exact False.elim (hb hxB)
      · exact hbound x hx hxB

theorem exists_fullCut_eq_closedCut (h : List ℝ) {lo B : ℝ} (hlo : lo < B) :
    ∃ A : ℝ, lo ≤ A ∧ A < B ∧ fullCut A h = closedCut B h := by
  obtain ⟨A,hloA,hAB,hbound⟩ := exists_empty_threshold_interval h hlo
  refine ⟨A,hloA,hAB,?_⟩
  unfold fullCut closedCut
  apply cutSchedule_congr_values
  intro p
  apply bool_eq_of_true_iff
  simp only [decide_eq_true_eq]
  constructor
  · intro hp
    by_contra hb
    exact not_lt_of_ge (hbound h[p] (List.getElem_mem p.isLt) (lt_of_not_ge hb)) hp
  · intro hp
    exact hAB.trans_le hp

end
end StrongSilver
