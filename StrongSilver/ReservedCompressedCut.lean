-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.InitialReservation
import StrongSilver.NumberedClosedCut
import StrongSilver.CompressedCutLog

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 1800000

namespace InitialReservation

def compressedSchedule {κ B μ : ℝ} {C : ScheduleCut} (R : InitialReservation κ B μ C) : List ℝ :=
  R.baseTracked.flatMap CutPhase.word

theorem compressed_sublist {κ B μ : ℝ} {C : ScheduleCut} (R : InitialReservation κ B μ C) :
    R.compressedSchedule.Sublist C.word :=
  (R.base_sublist.flatMap CutPhase.word).trans (List.sublist_append_left _ _)

theorem tracked_word {κ B μ : ℝ} {C : ScheduleCut} (R : InitialReservation κ B μ C) :
    R.assembly.trackedPhases.flatMap CutPhase.word = R.compressedSchedule := by
  rw [R.tracked_numbered,numberTrackedPhases_word]
  rfl

theorem compressed_cut {κ B μ : ℝ} {C : ScheduleCut} (R : InitialReservation κ B μ C)
    (hpiv : ∀ q ∈ C.phases, B ≤ q.pivot) (choose : ℕ → ℝ → Bool)
    (hselected : ∀ j b, B ≤ b → choose j b = true) :
    cutSchedule choose R.compressedSchedule =
      ⟨R.assembly.trackedPhases.flatMap (refinePhase choose),[]⟩ := by
  have hh := cut_numbered_phases_of_selected_pivots choose hselected 0 R.baseTracked
    (fun q hq => hpiv q (R.base_sublist.subset hq))
  rw [← R.tracked_numbered] at hh
  exact hh

theorem compressed_closed_cut {κ B μ : ℝ} {C : ScheduleCut} (R : InitialReservation κ B μ C)
    (hpiv : ∀ q ∈ C.phases, B ≤ q.pivot) (hgap : ∀ q ∈ C.phases, ∀ b ∈ q.gap, b < B) :
    closedCut B R.compressedSchedule = ⟨R.assembly.trackedPhases,[]⟩ := by
  have hh := closedCut_numbered_phases R.baseTracked (fun q hq => hpiv q (R.base_sublist.subset hq))
    (fun q hq => hgap q (R.base_sublist.subset hq))
  rw [← R.tracked_numbered] at hh
  exact hh

theorem phase_gap_cap {κ B μ : ℝ} {C : ScheduleCut} (R : InitialReservation κ B μ C)
    (hgap : ∀ q ∈ C.phases, ∀ b ∈ q.gap, 0 < b → b ≤ B) :
    ∀ q ∈ R.assembly.phases, ∀ b ∈ q.gap, 0 < b → b ≤ B := by
  intro q hq
  obtain ⟨z,hz,hgapEq,_⟩ := R.phase_data q hq
  simpa only [← hgapEq] using hgap z hz

theorem source_gap_mass {κ B μ : ℝ} {C : ScheduleCut} (R : InitialReservation κ B μ C) :
    phaseGapMass R.assembly.phases+Scalar.SignedIntervals.positiveMass C.terminal =
      Scalar.SignedIntervals.positiveMass C.unselected := by
  rw [R.phase_mass]
  exact C.unselected_positiveMass.symm

theorem compressed_log_eq {κ B μ P : ℝ} {C : ScheduleCut} (R : InitialReservation κ B μ C)
    (hpiv : ∀ q ∈ C.phases, B ≤ q.pivot) (choose : ℕ → ℝ → Bool)
    (hselected : ∀ j b, B ≤ b → choose j b = true) :
    cutLogProduct (cappedStep μ B) P 0 (cutSchedule choose R.compressedSchedule)-Real.log P =
      cappedPhaseLogSum μ B P (R.assembly.trackedPhases.flatMap (refinePhase choose)) := by
  rw [R.compressed_cut hpiv choose hselected]
  exact cutLogProduct_empty_terminal _ rfl

theorem compressed_power_eq {κ B μ P : ℝ} {C : ScheduleCut} (R : InitialReservation κ B μ C)
    (hpiv : ∀ q ∈ C.phases, B ≤ q.pivot) (choose : ℕ → ℝ → Bool)
    (hselected : ∀ j b, B ≤ b → choose j b = true) :
    cutPower (cappedStep μ B) P 0 (cutSchedule choose R.compressedSchedule)-P^nu =
      ((R.assembly.trackedPhases.flatMap (refinePhase choose)).map fun q => (gapPrefix (cappedStep μ B) q.gap+P)^nu).sum := by
  rw [R.compressed_cut hpiv choose hselected]
  exact cutPower_empty_terminal _ _ _ rfl

end InitialReservation
end
end StrongSilver
