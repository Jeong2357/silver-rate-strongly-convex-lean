-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.OrderedCutProperties

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 1800000

/-- Every actual sorted prefix admits a globally value-valid selector.
This supplies cutoff bounds even away from the finite schedule values,
while preserving every originally selected B-pivot. -/
theorem ordered_positionCut_value_selector (h : List ℝ) {A B : ℝ} (hAB : A ≤ B) {i : ℕ}
    (hi : i ≤ (orderedPositions h (eligibleIndices h Finset.univ A B)).length) :
    ∃ t : ℝ, ∃ choose : ℕ → ℝ → Bool, A ≤ t ∧ t ≤ B ∧
      positionCut (fun _ b => decide (B ≤ b)) h ((orderedPositions h (eligibleIndices h Finset.univ A B)).take i) = cutSchedule choose h ∧
      (∀ j b, choose j b = true → t ≤ b) ∧ (∀ j b, choose j b = false → b ≤ t) ∧
      (∀ j b, B ≤ b → choose j b = true) := by
  cases i with
  | zero =>
    refine ⟨B,(fun _ b => decide (B ≤ b)),hAB,le_rfl,?_,?_,?_,?_⟩
    · simp only [List.take_zero,positionCut_nil_closed,closedCut]
    · intro j b hb
      exact of_decide_eq_true hb
    · intro j b hb
      exact (lt_of_not_ge (of_decide_eq_false hb)).le
    · intro j b hb
      exact decide_eq_true hb
  | succ i =>
    have hj : i < (sortedScheduleIndices h (eligibleIndices h Finset.univ A B)).length := by
      simpa only [orderedPositions,List.length_map] using Nat.lt_of_succ_le hi
    let p := (sortedScheduleIndices h (eligibleIndices h Finset.univ A B))[i]
    have hp := mem_sortedScheduleIndices.mp (List.getElem_mem hj)
    have hr := (Finset.mem_filter.mp hp).2
    refine ⟨h[p],(fun j b => decide (h[p] < b ∨ b = h[p] ∧ j < p.val+1)),hr.1.le,hr.2.le,?_,?_,?_,?_⟩
    · exact ordered_positionCut_partialTie h A B hj
    · intro j b hb
      rcases of_decide_eq_true hb with hb | ⟨hb,_⟩
      · exact hb.le
      · exact hb.ge
    · intro j b hb
      have hn := of_decide_eq_false hb
      exact le_of_not_gt (fun hh => hn (Or.inl hh))
    · intro j b hb
      exact decide_eq_true (Or.inl (hr.2.trans_le hb))

end
end StrongSilver
