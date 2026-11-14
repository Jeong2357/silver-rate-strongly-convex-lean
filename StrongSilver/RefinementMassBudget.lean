-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CompleteInitialCutTrace
import StrongSilver.InitialAssemblyCost
import StrongSilver.WorkingGlobalLogBudget

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 1400000

theorem phaseGapMass_append (qs rs : List CutPhase) : phaseGapMass (qs++rs) = phaseGapMass qs+phaseGapMass rs := by
  simp [phaseGapMass,List.map_append,List.sum_append]

theorem refinePhase_gapMass_le (choose : ℕ → ℝ → Bool) (q : CutPhase) :
    phaseGapMass (refinePhase choose q) ≤ Scalar.SignedIntervals.positiveMass q.gap := by
  let C := cutScheduleFrom choose (q.index-q.gap.length) q.gap
  have hm := C.unselected_positiveMass
  have he : phaseGapMass (refinePhase choose q) = Scalar.SignedIntervals.positiveMass C.unselected := by
    change phaseGapMass (C.phases++[⟨C.terminal,q.pivot,q.index⟩]) = _
    rw [phaseGapMass_append]
    simpa only [phaseGapMass,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using hm.symm
  exact he.trans_le (positiveMass_sublist_le (cutScheduleFrom_unselected_sublist choose _ _))

theorem refinePhases_gapMass_le (choose : ℕ → ℝ → Bool) (qs : List CutPhase) :
    phaseGapMass (qs.flatMap (refinePhase choose)) ≤ phaseGapMass qs := by
  induction qs with
  | nil => exact le_rfl
  | cons q qs ih =>
    rw [List.flatMap_cons,phaseGapMass_append]
    exact add_le_add (refinePhase_gapMass_le choose q) ih

theorem InitialCutAssembly.refined_gapMass_budget (s : InitialCutAssembly) (choose : ℕ → ℝ → Bool) :
    phaseGapMass (s.trackedPhases.flatMap (refinePhase choose))+phaseGapMass s.reserved ≤ phaseGapMass s.phases := by
  have hh := s.weight_partition (fun q => Scalar.SignedIntervals.positiveMass q.gap)
  have hr := refinePhases_gapMass_le choose s.trackedPhases
  change phaseGapMass s.phases = phaseGapMass s.trackedPhases+phaseGapMass s.reserved at hh
  linarith only [hh,hr]

theorem CompleteInitialCutAssembly.weight_partition (s : CompleteInitialCutAssembly) (w : CutPhase → ℝ) :
    (s.phases.map w).sum = (s.trackedPhases.map w).sum+(s.reserved.map w).sum := by
  cases s with
  | scalar I => simp [phases,trackedPhases,reserved]
  | positive s => exact s.weight_partition w
  | leadingBlock I c d s =>
    simp only [phases,trackedPhases,reserved,List.map_append,List.sum_append,List.map_cons,List.sum_cons]
    rw [s.weight_partition w]
    ring
  | leadingEnd I c => simp [phases,trackedPhases,reserved]

theorem CompleteInitialCutAssembly.refined_gapMass_budget (s : CompleteInitialCutAssembly) (choose : ℕ → ℝ → Bool) :
    phaseGapMass (s.trackedPhases.flatMap (refinePhase choose))+phaseGapMass s.reserved ≤ phaseGapMass s.phases := by
  have hh := s.weight_partition (fun q => Scalar.SignedIntervals.positiveMass q.gap)
  have hr := refinePhases_gapMass_le choose s.trackedPhases
  change phaseGapMass s.phases = phaseGapMass s.trackedPhases+phaseGapMass s.reserved at hh
  linarith only [hh,hr]

end
end StrongSilver
