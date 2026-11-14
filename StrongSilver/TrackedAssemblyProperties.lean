-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.TrackedAssemblyNumbering
import StrongSilver.InitialMarkedCount
import Mathlib.Data.List.Flatten

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 1800000

theorem badPhaseCount_eq_mapped {α : Type*} (good : α → Bool) (qs : List α) :
    badPhaseCount good qs = badPhaseCount id (qs.map good) := by
  induction qs with
  | nil => rfl
  | cons q qs ih => simp only [badPhaseCount_cons,List.map_cons,ih,id_eq]

namespace InitialCutAssembly

theorem trackedPhases_sublist (s : InitialCutAssembly) : s.trackedPhases.Sublist s.phases := by
  induction s with
  | terminal => rfl
  | tracked q s ih => exact ih.cons_cons q
  | block q I c d s ih =>
    apply ih.trans
    simpa only [phases,List.append_assoc,List.cons_append,List.singleton_append,List.nil_append] using
      List.sublist_append_right (q::(I++[c,d])) s.phases
  | terminalBlock q I c => exact List.nil_sublist _
  | noConnector q I => exact List.nil_sublist _

end InitialCutAssembly

namespace CompleteInitialCutAssembly

theorem trackedPhases_sublist (s : CompleteInitialCutAssembly) : s.trackedPhases.Sublist s.phases := by
  cases s with
  | scalar I => exact List.nil_sublist _
  | positive s => exact s.trackedPhases_sublist
  | leadingBlock I c d s =>
    apply s.trackedPhases_sublist.trans
    simpa only [phases,List.append_assoc,List.cons_append,List.singleton_append,List.nil_append] using
      List.sublist_append_right (I++[c,d]) s.phases
  | leadingEnd I c => exact List.nil_sublist _

theorem numberTracked_phase_data (i : ℕ) (s : CompleteInitialCutAssembly) {q : CutPhase}
    (hq : q ∈ (s.numberTracked i).phases) :
    ∃ z ∈ s.phases, z.gap = q.gap ∧ z.pivot = q.pivot := by
  let f : CutPhase → List ℝ × ℝ := fun q => (q.gap,q.pivot)
  have hm : f q ∈ (s.numberTracked i).phases.map f := List.mem_map.mpr ⟨q,hq,rfl⟩
  rw [s.numberTracked_phases_map f (fun _ _ => rfl) i] at hm
  obtain ⟨z,hz,he⟩ := List.mem_map.mp hm
  exact ⟨z,hz,congrArg Prod.fst he,congrArg Prod.snd he⟩

theorem numberTracked_badPhaseCount {good : CutPhase → Bool} (hg : ∀ q i, good (q.withIndex i) = good q)
    (i : ℕ) (s : CompleteInitialCutAssembly) :
    badPhaseCount good (s.numberTracked i).phases = badPhaseCount good s.phases := by
  rw [badPhaseCount_eq_mapped,s.numberTracked_phases_map good hg i,← badPhaseCount_eq_mapped]

theorem numberTracked_initialMarked_count (κ B μ : ℝ) (i : ℕ) (s : CompleteInitialCutAssembly) :
    badPhaseCount (initialMarkedGood κ B μ) (s.numberTracked i).phases = badPhaseCount (initialMarkedGood κ B μ) s.phases :=
  s.numberTracked_badPhaseCount (fun _ _ => rfl) i

theorem numberTracked_tracked_word_sublist (i : ℕ) (s : CompleteInitialCutAssembly) (t : List ℝ) :
    ((s.numberTracked i).trackedPhases.flatMap CutPhase.word).Sublist (s.phases.flatMap CutPhase.word++t) := by
  rw [s.numberTracked_trackedPhases,numberTrackedPhases_word]
  exact (s.trackedPhases_sublist.flatMap CutPhase.word).trans (List.sublist_append_left _ _)

end CompleteInitialCutAssembly
end
end StrongSilver
