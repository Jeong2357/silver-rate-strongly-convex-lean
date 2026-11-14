-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.EligibleWeights
import StrongSilver.PowerReservePropagation
import StrongSilver.ScheduleCutPartition

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 1800000

theorem closedCut_unselected {B : ℝ} {h : List ℝ} {b : ℝ} (hb : b ∈ (closedCut B h).unselected) : b < B := by
  apply cutScheduleFrom_unselected_property (fun b => b < B) ?_ 0 h b hb
  intro i b he
  exact lt_of_not_ge (of_decide_eq_false he)

theorem ordered_positionCut_count (h : List ℝ) (A B : ℝ) {i : ℕ}
    (hi : i ≤ (orderedPositions h (eligibleIndices h Finset.univ A B)).length) :
    (positionCut (fun _ b => decide (B ≤ b)) h ((orderedPositions h (eligibleIndices h Finset.univ A B)).take i)).phases.length =
      countAbove h B+i := by
  let ps := orderedPositions h (eligibleIndices h Finset.univ A B)
  have hv : ∀ p ∈ ps, p < h.length := orderedPositions_valid h _
  have hf : ∀ p (hp : p ∈ ps), decide (B ≤ (h[p]'(hv p hp))) = false := by
    intro p hp
    have hb := (eligible_positions_range h Finset.univ A B p hp).2
    rw [stepAt_eq (hv p hp)] at hb
    exact decide_eq_false (not_le.mpr hb)
  have hh := position_cut_count_after (fun _ b => decide (B ≤ b)) h ps
    (orderedPositions_nodup h _) hv hf i hi
  simpa only [positionCut_nil_closed,closedCut_count] using hh

/-- Every sorted refinement prefix is a genuine threshold cut with the
paper's chronological tie rule, and its threshold stays inside the band. -/
theorem ordered_positionCut_band (h : List ℝ) {A B : ℝ} (hAB : A ≤ B) {i : ℕ}
    (hi : i ≤ (orderedPositions h (eligibleIndices h Finset.univ A B)).length) :
    let C := positionCut (fun _ b => decide (B ≤ b)) h
      ((orderedPositions h (eligibleIndices h Finset.univ A B)).take i)
    ∃ t : ℝ, A ≤ t ∧ t ≤ B ∧ (∀ q ∈ C.phases, t ≤ q.pivot) ∧ (∀ b ∈ C.unselected, b ≤ t) := by
  cases i with
  | zero =>
    refine ⟨B,hAB,le_rfl,?_,?_⟩
    · simpa only [List.take_zero,positionCut_nil_closed] using fun (q : CutPhase) (hq : q ∈ (closedCut B h).phases) => closedCut_pivot hq
    · simpa only [List.take_zero,positionCut_nil_closed] using fun (b : ℝ) (hb : b ∈ (closedCut B h).unselected) => (closedCut_unselected hb).le
  | succ i =>
    have hj : i < (sortedScheduleIndices h (eligibleIndices h Finset.univ A B)).length := by
      simpa only [orderedPositions,List.length_map] using Nat.lt_of_succ_le hi
    let p := (sortedScheduleIndices h (eligibleIndices h Finset.univ A B))[i]
    have hp := mem_sortedScheduleIndices.mp (List.getElem_mem hj)
    have hr := (Finset.mem_filter.mp hp).2
    have he := ordered_positionCut_partialTie h A B hj
    refine ⟨h[p],hr.1.le,hr.2.le,?_,?_⟩
    · intro q hq
      rw [he] at hq
      exact partialTieCut_pivot hq
    · intro b hb
      rw [he] at hb
      exact partialTieCut_unselected hb

end
end StrongSilver
