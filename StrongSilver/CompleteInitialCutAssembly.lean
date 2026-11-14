-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.InitialCutAssembly

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 1800000

inductive CompleteInitialCutAssembly where
  | scalar (inside : List CutPhase)
  | positive (suffix : InitialCutAssembly)
  | leadingBlock (inside : List CutPhase) (right provider : CutPhase) (suffix : InitialCutAssembly)
  | leadingEnd (inside : List CutPhase) (right : CutPhase)

namespace CompleteInitialCutAssembly

def phases : CompleteInitialCutAssembly → List CutPhase
  | .scalar I => I
  | .positive s => s.phases
  | .leadingBlock I c d s => I++(c::d::s.phases)
  | .leadingEnd I c => I++[c]

def trackedPhases : CompleteInitialCutAssembly → List CutPhase
  | .scalar _ => []
  | .positive s => s.trackedPhases
  | .leadingBlock _ _ _ s => s.trackedPhases
  | .leadingEnd _ _ => []

def reserved : CompleteInitialCutAssembly → List CutPhase
  | .scalar I => I
  | .positive s => s.reserved
  | .leadingBlock I c d s => I++(c::d::s.reserved)
  | .leadingEnd I c => I++[c]

def WellFormed (good : CutPhase → Bool) : CompleteInitialCutAssembly → Prop
  | .scalar _ => True
  | .positive s => s.WellFormed good
  | .leadingBlock _ c d s => good c = true ∧ good d = true ∧ s.WellFormed good
  | .leadingEnd _ c => good c = true

def Counted (good : CutPhase → Bool) : CompleteInitialCutAssembly → Prop
  | .scalar I => I.length ≤ 7*badPhaseCount good I
  | .positive s => s.Counted good
  | .leadingBlock I _ _ s => I.length+2 ≤ 7*badPhaseCount good I ∧ s.Counted good
  | .leadingEnd I _ => I.length+1 ≤ 7*badPhaseCount good I

theorem reserved_count_bound {good : CutPhase → Bool} {s : CompleteInitialCutAssembly}
    (hs : s.WellFormed good) (hc : s.Counted good) : s.reserved.length ≤ 7*badPhaseCount good s.phases := by
  cases s with
  | scalar I => exact hc
  | positive s => exact s.reserved_count_bound hs hc
  | leadingBlock I c d s =>
    have hh := s.reserved_count_bound hs.2.2 hc.2
    have hsize := hc.1
    simp only [reserved,phases,List.length_append,List.length_cons,badPhaseCount_append,
      badPhaseCount_cons,hs.1,hs.2.1,↓reduceIte,zero_add]
    omega
  | leadingEnd I c =>
    change good c = true at hs
    change I.length+1 ≤ 7*badPhaseCount good I at hc
    simpa [reserved,phases,badPhaseCount_append,badPhaseCount_cons,hs,Nat.add_comm] using hc

end CompleteInitialCutAssembly

theorem exists_complete_initial_cutAssembly (good : CutPhase → Bool) (qs : List CutPhase) :
    ∃ s : CompleteInitialCutAssembly, s.phases = qs ∧ s.WellFormed good ∧ s.Counted good ∧
      s.reserved.length ≤ 7*badPhaseCount good qs := by
  cases qs with
  | nil => exact ⟨.scalar [],rfl,True.intro,by simp [CompleteInitialCutAssembly.Counted],by simp [CompleteInitialCutAssembly.reserved]⟩
  | cons q qs =>
    by_cases hq : good q = true
    · obtain ⟨s,hph,hs,hc⟩ := exists_initial_cutAssembly good q qs hq
      exact ⟨.positive s,hph,hs,hc,by simpa only [CompleteInitialCutAssembly.reserved,hph] using s.reserved_count_bound hs hc⟩
    · have hqfalse := Bool.eq_false_iff.mpr hq
      have hsize := reserveRun_three_reserved_size (qs := qs) hqfalse
      generalize hR : reserveRun good 3 (q::qs) = R
      rcases R with ⟨I,rem⟩
      rw [hR] at hsize
      change I.length+3 ≤ 7*badPhaseCount good I at hsize
      have hpart := ReservedRun.partition good 3 (q::qs)
      rw [hR] at hpart
      have hg := ReservedRun.remaining_good good 3 (q::qs)
      rw [hR] at hg
      suffices h : ∃ s : CompleteInitialCutAssembly, s.phases = q::qs ∧ s.WellFormed good ∧ s.Counted good by
        obtain ⟨s,hph,hs,hc⟩ := h
        exact ⟨s,hph,hs,hc,by simpa only [hph] using s.reserved_count_bound hs hc⟩
      cases rem with
      | nil =>
        exact ⟨.scalar I,by simpa only [CompleteInitialCutAssembly.phases,List.append_nil] using hpart,
          True.intro,by change I.length ≤ 7*badPhaseCount good I; omega⟩
      | cons c tail =>
        obtain ⟨hc,htail⟩ := hg c tail rfl
        cases tail with
        | nil => exact ⟨.leadingEnd I c,hpart,hc,by change I.length+1 ≤ 7*badPhaseCount good I; omega⟩
        | cons d tail =>
          have hd : good d = true := (List.all_eq_true.mp htail) d (by simp)
          cases tail with
          | nil => exact ⟨.leadingBlock I c d .terminal,hpart,⟨hc,hd,True.intro⟩,
              ⟨by change I.length+2 ≤ 7*badPhaseCount good I; omega,True.intro⟩⟩
          | cons e es =>
            have he : good e = true := (List.all_eq_true.mp htail) e (by simp)
            obtain ⟨s,hph,hs,hcount⟩ := exists_initial_cutAssembly good e es he
            refine ⟨.leadingBlock I c d s,?_,⟨hc,hd,hs⟩,⟨?_,hcount⟩⟩
            · simpa only [CompleteInitialCutAssembly.phases,hph] using hpart
            · change I.length+2 ≤ 7*badPhaseCount good I
              omega

end
end StrongSilver
