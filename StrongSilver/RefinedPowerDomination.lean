-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CutGapShape
import StrongSilver.CutConcatenation
import StrongSilver.ReservedCompressedCut

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 2400000

theorem gapPower_nonnegative (φ : ℝ → ℝ) {P : ℝ} (hP : 0 ≤ P) (q : CutPhase) :
    0 ≤ (gapPrefix φ q.gap+P)^nu := Real.rpow_nonneg (add_nonneg (gapPrefix_nonnegative φ q.gap) hP) nu

/-- Refining all original nonterminal gaps contributes only part of the
power of the actual full cut; the remaining terminal factors are nonnegative. -/
theorem refined_phase_power_le_full_cut (φ : ℝ → ℝ) {A P : ℝ} (hP : 0 ≤ P) (C : ScheduleCut)
    (hpiv : ∀ q ∈ C.phases, A < q.pivot) :
    ((C.phases.flatMap (refinePhase (fun _ b => decide (A < b)))).map fun q => (gapPrefix φ q.gap+P)^nu).sum ≤
      cutPower φ P 0 (fullCut A C.word) := by
  let choose : ℕ → ℝ → Bool := fun _ b => decide (A < b)
  let D := cutScheduleFrom choose (C.phases.flatMap CutPhase.word).length C.terminal
  have hnum := cutScheduleFrom_numbered_phases choose 0 C.phases (fun q hq _ => decide_eq_true (hpiv q hq))
  have hcut : fullCut A C.word =
      ⟨(numberTrackedPhases 0 C.phases).flatMap (refinePhase choose)++D.phases,D.terminal⟩ := by
    change cutScheduleFrom choose 0 (C.phases.flatMap CutPhase.word++C.terminal) = _
    rw [cutScheduleFrom_append,hnum,Nat.zero_add]
    rfl
  have hmap := numberTrackedPhases_refined_map_gap (fun g => (gapPrefix φ g+P)^nu)
    (fun b => decide (A < b)) 0 C.phases
  rw [hcut,cutPower_eq_phase_sum]
  simp only [List.map_append,List.sum_append]
  rw [hmap]
  have hphase : 0 ≤ (D.phases.map fun q => (gapPrefix φ q.gap+P)^nu).sum := by
    apply List.sum_nonneg
    intro x hx
    obtain ⟨q,_,rfl⟩ := List.mem_map.mp hx
    exact gapPower_nonnegative φ hP q
  have hterminal : 0 ≤ (gapPrefix φ D.terminal+P+0)^nu :=
    Real.rpow_nonneg (by have hh := gapPrefix_nonnegative φ D.terminal; linarith only [hh,hP]) nu
  linarith only [hphase,hterminal]

/-- Tracked gaps at a full threshold are also gaps of the original full
cut. Index compression changes none of their actual prefix maxima. -/
theorem InitialReservation.compressed_full_cut_power_le {κ B μ A P : ℝ} {C : ScheduleCut}
    (R : InitialReservation κ B μ C) (φ : ℝ → ℝ) (hP : 0 ≤ P) (hAB : A < B)
    (hpiv : ∀ q ∈ C.phases, B ≤ q.pivot) :
    cutPower φ P 0 (fullCut A R.compressedSchedule)-P^nu ≤ cutPower φ P 0 (fullCut A C.word) := by
  let choose : ℕ → ℝ → Bool := fun _ b => decide (A < b)
  have hselected : ∀ j b, B ≤ b → choose j b = true := fun _ _ hb => decide_eq_true (hAB.trans_le hb)
  have hcomp := R.compressed_cut hpiv choose hselected
  have ht : (fullCut A R.compressedSchedule).terminal = [] := by
    change (cutSchedule choose R.compressedSchedule).terminal = []
    rw [hcomp]
  have hpower := cutPower_empty_terminal φ P (fullCut A R.compressedSchedule) ht
  have hphases : (fullCut A R.compressedSchedule).phases = R.assembly.trackedPhases.flatMap (refinePhase choose) := by
    change (cutSchedule choose R.compressedSchedule).phases = _
    rw [hcomp]
  rw [hphases,R.tracked_numbered,numberTrackedPhases_refined_map_gap (fun g => (gapPrefix φ g+P)^nu) (fun b => decide (A < b))] at hpower
  rw [hpower]
  have hs := list_weight_sublist_le (fun q => (gapPrefix φ q.gap+P)^nu) (gapPower_nonnegative φ hP)
    (R.base_sublist.flatMap (refinePhase choose))
  exact hs.trans (refined_phase_power_le_full_cut φ hP C (fun q hq => hAB.trans_le (hpiv q hq)))

end
end StrongSilver
