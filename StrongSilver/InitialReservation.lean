-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.TrackedAssemblyProperties

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 2000000

theorem CompleteInitialCutAssembly.length_partition (s : CompleteInitialCutAssembly) :
    s.phases.length = s.trackedPhases.length+s.reserved.length := by
  cases s with
  | scalar I => simp [phases,trackedPhases,reserved]
  | positive s => exact s.length_partition
  | leadingBlock I c d s =>
    have hh := s.length_partition
    simp only [phases,trackedPhases,reserved,List.length_append,List.length_cons]
    omega
  | leadingEnd I c => simp [phases,trackedPhases,reserved]

/-- A fixed initial reservation, with the tracked phases numbered in their
compressed schedule and all reserved actual steps retained in the source. -/
structure InitialReservation (κ B μ : ℝ) (C : ScheduleCut) where
  assembly : CompleteInitialCutAssembly
  baseTracked : List CutPhase
  source_word : assembly.word C.terminal = C.word
  tracked_numbered : assembly.trackedPhases = numberTrackedPhases 0 baseTracked
  base_sublist : baseTracked.Sublist C.phases
  wellFormed : assembly.WellFormed (initialMarkedGood κ B μ)
  counted : assembly.Counted (initialMarkedGood κ B μ)
  reserved_count : assembly.reserved.length ≤ 7*badPhaseCount (initialPhaseTests κ) C.phases
  bad_count : badPhaseCount (initialMarkedGood κ B μ) assembly.phases ≤ badPhaseCount (initialPhaseTests κ) C.phases
  tracked_count : C.phases.length ≤ baseTracked.length+7*badPhaseCount (initialPhaseTests κ) C.phases
  phase_data : ∀ q ∈ assembly.phases, ∃ z ∈ C.phases, z.gap = q.gap ∧ z.pivot = q.pivot
  phase_mass : phaseGapMass assembly.phases = phaseGapMass C.phases

theorem nonempty_initial_reservation {κ B μ : ℝ} (hκ : 1 ≤ κ) (hB : 2 ≤ B) (hBκ : B ≤ κ/4)
    (hμ : 1/κ ≤ μ) (hμu : μ ≤ 9/(8*κ)) (C : ScheduleCut)
    (hpiv : ∀ q ∈ C.phases, B ≤ q.pivot) (hgap : ∀ q ∈ C.phases, ∀ b ∈ q.gap, 0 < b → b ≤ B) :
    Nonempty (InitialReservation κ B μ C) := by
  let good := initialMarkedGood κ B μ
  obtain ⟨s0,hph,hs,hc,hres⟩ := exists_complete_initial_cutAssembly good C.phases
  have hB0 : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hmarked := initial_marked_count_le hκ hB0 hBκ hμ hμu C.phases hpiv hgap
  have hreserved : s0.reserved.length ≤ 7*badPhaseCount (initialPhaseTests κ) C.phases := hres.trans (Nat.mul_le_mul_left 7 hmarked)
  refine ⟨{
    assembly := s0.numberTracked 0
    baseTracked := s0.trackedPhases
    source_word := ?_
    tracked_numbered := s0.numberTracked_trackedPhases 0
    base_sublist := ?_
    wellFormed := s0.numberTracked_wellFormed (fun _ _ => rfl) 0 hs
    counted := s0.numberTracked_counted 0 hc
    reserved_count := ?_
    bad_count := ?_
    tracked_count := ?_
    phase_data := ?_
    phase_mass := ?_
  }⟩
  · simp only [CompleteInitialCutAssembly.word,s0.numberTracked_word,hph,ScheduleCut.word]
  · simpa only [hph] using s0.trackedPhases_sublist
  · simpa only [s0.numberTracked_reserved] using hreserved
  · rw [s0.numberTracked_initialMarked_count,hph]
    exact hmarked
  · have hh := s0.length_partition
    rw [hph] at hh
    omega
  · intro q hq
    obtain ⟨z,hz,hzq⟩ := s0.numberTracked_phase_data 0 hq
    rw [hph] at hz
    exact ⟨z,hz,hzq⟩
  · have hh := s0.numberTracked_phases_map (fun q => Scalar.SignedIntervals.positiveMass q.gap) (fun _ _ => rfl) 0
    simpa only [phaseGapMass,hph] using congrArg List.sum hh

end
end StrongSilver
