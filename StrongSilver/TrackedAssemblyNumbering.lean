-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.TrackedPhaseNumbering
import StrongSilver.CompleteInitialCutAssembly

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 1800000

namespace InitialCutAssembly

def numberTracked (i : ℕ) : InitialCutAssembly → InitialCutAssembly
  | .terminal => .terminal
  | .tracked q s => .tracked (q.withIndex (i+q.gap.length)) (s.numberTracked (i+q.word.length))
  | .block q I c d s => .block q I c d (s.numberTracked i)
  | .terminalBlock q I c => .terminalBlock q I c
  | .noConnector q I => .noConnector q I

theorem numberTracked_trackedPhases (i : ℕ) (s : InitialCutAssembly) :
    (s.numberTracked i).trackedPhases = numberTrackedPhases i s.trackedPhases := by
  induction s generalizing i <;> simp_all [numberTracked,trackedPhases,numberTrackedPhases]

theorem numberTracked_reserved (i : ℕ) (s : InitialCutAssembly) : (s.numberTracked i).reserved = s.reserved := by
  induction s generalizing i <;> simp_all [numberTracked,reserved]

theorem numberTracked_phases_map {α : Type*} (f : CutPhase → α) (hf : ∀ q i, f (q.withIndex i) = f q)
    (i : ℕ) (s : InitialCutAssembly) : (s.numberTracked i).phases.map f = s.phases.map f := by
  induction s generalizing i <;> simp_all [numberTracked,phases,List.map_append,hf]

theorem numberTracked_word (i : ℕ) (s : InitialCutAssembly) :
    (s.numberTracked i).phases.flatMap CutPhase.word = s.phases.flatMap CutPhase.word := by
  simpa only [List.flatMap_def] using congrArg List.flatten (s.numberTracked_phases_map CutPhase.word (fun _ _ => rfl) i)

theorem numberTracked_wellFormed {good : CutPhase → Bool} (hg : ∀ q i, good (q.withIndex i) = good q)
    (i : ℕ) (s : InitialCutAssembly) (hs : s.WellFormed good) : (s.numberTracked i).WellFormed good := by
  induction s generalizing i <;> simp_all [numberTracked,WellFormed,hg]

theorem numberTracked_counted {good : CutPhase → Bool} (i : ℕ) (s : InitialCutAssembly)
    (hs : s.Counted good) : (s.numberTracked i).Counted good := by
  induction s generalizing i <;> simp_all [numberTracked,Counted]

end InitialCutAssembly

namespace CompleteInitialCutAssembly

def numberTracked (i : ℕ) : CompleteInitialCutAssembly → CompleteInitialCutAssembly
  | .scalar I => .scalar I
  | .positive s => .positive (s.numberTracked i)
  | .leadingBlock I c d s => .leadingBlock I c d (s.numberTracked i)
  | .leadingEnd I c => .leadingEnd I c

theorem numberTracked_trackedPhases (i : ℕ) (s : CompleteInitialCutAssembly) :
    (s.numberTracked i).trackedPhases = numberTrackedPhases i s.trackedPhases := by
  cases s <;> simp only [numberTracked,trackedPhases,InitialCutAssembly.numberTracked_trackedPhases,numberTrackedPhases]

theorem numberTracked_reserved (i : ℕ) (s : CompleteInitialCutAssembly) : (s.numberTracked i).reserved = s.reserved := by
  cases s <;> simp only [numberTracked,reserved,InitialCutAssembly.numberTracked_reserved]

theorem numberTracked_phases_map {α : Type*} (f : CutPhase → α) (hf : ∀ q i, f (q.withIndex i) = f q)
    (i : ℕ) (s : CompleteInitialCutAssembly) : (s.numberTracked i).phases.map f = s.phases.map f := by
  cases s <;> simp only [numberTracked,phases,List.map_append,List.map_cons,InitialCutAssembly.numberTracked_phases_map f hf]

theorem numberTracked_word (i : ℕ) (s : CompleteInitialCutAssembly) :
    (s.numberTracked i).phases.flatMap CutPhase.word = s.phases.flatMap CutPhase.word := by
  simpa only [List.flatMap_def] using congrArg List.flatten (s.numberTracked_phases_map CutPhase.word (fun _ _ => rfl) i)

theorem numberTracked_wellFormed {good : CutPhase → Bool} (hg : ∀ q i, good (q.withIndex i) = good q)
    (i : ℕ) (s : CompleteInitialCutAssembly) (hs : s.WellFormed good) : (s.numberTracked i).WellFormed good := by
  cases s <;> simp_all [numberTracked,WellFormed,InitialCutAssembly.numberTracked_wellFormed hg]

theorem numberTracked_counted {good : CutPhase → Bool} (i : ℕ) (s : CompleteInitialCutAssembly)
    (hs : s.Counted good) : (s.numberTracked i).Counted good := by
  cases s <;> simp_all [numberTracked,Counted,InitialCutAssembly.numberTracked_counted]

end CompleteInitialCutAssembly
end
end StrongSilver
