-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.InitialReservedRunCount
import StrongSilver.ScheduleCut

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 1800000

inductive InitialCutAssembly where
  | terminal
  | tracked (q : CutPhase) (suffix : InitialCutAssembly)
  | block (left : CutPhase) (inside : List CutPhase) (right provider : CutPhase) (suffix : InitialCutAssembly)
  | terminalBlock (left : CutPhase) (inside : List CutPhase) (right : CutPhase)
  | noConnector (left : CutPhase) (inside : List CutPhase)

namespace InitialCutAssembly

def phases : InitialCutAssembly → List CutPhase
  | .terminal => []
  | .tracked q s => q::s.phases
  | .block q I c d s => q::(I++(c::d::s.phases))
  | .terminalBlock q I c => q::(I++[c])
  | .noConnector q I => q::I

def WellFormed (good : CutPhase → Bool) : InitialCutAssembly → Prop
  | .terminal => True
  | .tracked q s => good q = true ∧ s.WellFormed good
  | .block q _ c d s => good q = true ∧ good c = true ∧ good d = true ∧ s.WellFormed good
  | .terminalBlock q _ c => good q = true ∧ good c = true
  | .noConnector q _ => good q = true

def Counted (good : CutPhase → Bool) : InitialCutAssembly → Prop
  | .terminal => True
  | .tracked _ s => s.Counted good
  | .block _ I _ _ s => I.length+3 ≤ 7*badPhaseCount good I ∧ s.Counted good
  | .terminalBlock _ I _ => I.length+2 ≤ 7*badPhaseCount good I
  | .noConnector _ I => I.length+1 ≤ 7*badPhaseCount good I

def trackedPhases : InitialCutAssembly → List CutPhase
  | .terminal => []
  | .tracked q s => q::s.trackedPhases
  | .block _ _ _ _ s => s.trackedPhases
  | .terminalBlock _ _ _ => []
  | .noConnector _ _ => []

def reserved : InitialCutAssembly → List CutPhase
  | .terminal => []
  | .tracked _ s => s.reserved
  | .block q I c d s => q::(I++(c::d::s.reserved))
  | .terminalBlock q I c => q::(I++[c])
  | .noConnector q I => q::I

theorem length_partition (s : InitialCutAssembly) : s.phases.length = s.trackedPhases.length+s.reserved.length := by
  induction s <;> simp_all [phases,trackedPhases,reserved] <;> omega

theorem reserved_count_bound {good : CutPhase → Bool} {s : InitialCutAssembly}
    (hs : s.WellFormed good) (hc : s.Counted good) : s.reserved.length ≤ 7*badPhaseCount good s.phases := by
  induction s with
  | terminal => simp [reserved]
  | tracked q s ih =>
    have hh := ih hs.2 hc
    simpa only [reserved,phases,badPhaseCount_cons,hs.1,↓reduceIte,zero_add] using hh
  | block q I c d s ih =>
    have hh := ih hs.2.2.2 hc.2
    have hsize := hc.1
    simp only [reserved,phases,List.length_cons,List.length_append,badPhaseCount_cons,
      badPhaseCount_append,hs.1,hs.2.1,hs.2.2.1,↓reduceIte,zero_add]
    omega
  | terminalBlock q I c =>
    have hq := hs.1
    have hright := hs.2
    change good q = true at hq
    change good c = true at hright
    change I.length+2 ≤ 7*badPhaseCount good I at hc
    simp only [reserved,phases,List.length_cons,List.length_append,List.length_singleton,
      badPhaseCount_append,badPhaseCount_cons,badPhaseCount_nil,hq,hright,↓reduceIte,zero_add,add_zero]
    omega
  | noConnector q I =>
    change good q = true at hs
    change I.length+1 ≤ 7*badPhaseCount good I at hc
    simpa [reserved,phases,badPhaseCount_cons,hs,Nat.add_comm] using hc

end InitialCutAssembly

theorem exists_initial_cutAssembly (good : CutPhase → Bool) (q : CutPhase) (qs : List CutPhase) (hq : good q = true) :
    ∃ s : InitialCutAssembly, s.phases = q::qs ∧ s.WellFormed good ∧ s.Counted good := by
  have aux : ∀ fuel : ℕ, ∀ q qs, qs.length < fuel → good q = true →
      ∃ s : InitialCutAssembly, s.phases = q::qs ∧ s.WellFormed good ∧ s.Counted good := by
    intro fuel
    induction fuel with
    | zero => intro q qs hf; omega
    | succ fuel ih =>
      intro q qs hf hq
      cases qs with
      | nil => exact ⟨.tracked q .terminal,rfl,⟨hq,True.intro⟩,True.intro⟩
      | cons r rs =>
        by_cases hr : good r = true
        · obtain ⟨s,hph,hs,hc⟩ := ih r rs (by simp only [List.length_cons] at hf; omega) hr
          exact ⟨.tracked q s,by simp only [InitialCutAssembly.phases,hph],⟨hq,hs⟩,hc⟩
        · have hrfalse := Bool.eq_false_iff.mpr hr
          have hsize := reserveRun_three_reserved_size (qs := rs) hrfalse
          generalize hR : reserveRun good 3 (r::rs) = R
          rcases R with ⟨I,rem⟩
          rw [hR] at hsize
          change I.length+3 ≤ 7*badPhaseCount good I at hsize
          have hpart := ReservedRun.partition good 3 (r::rs)
          rw [hR] at hpart
          have hlen := ReservedRun.remaining_length_le good 3 (r::rs)
          rw [hR] at hlen
          have hg := ReservedRun.remaining_good good 3 (r::rs)
          rw [hR] at hg
          cases rem with
          | nil =>
            exact ⟨.noConnector q I,by simpa only [InitialCutAssembly.phases,List.append_nil] using congrArg (List.cons q) hpart,
              hq,by change I.length+1 ≤ 7*badPhaseCount good I; omega⟩
          | cons c tail =>
            obtain ⟨hc,htail⟩ := hg c tail rfl
            cases tail with
            | nil =>
              exact ⟨.terminalBlock q I c,congrArg (List.cons q) hpart,⟨hq,hc⟩,
                by change I.length+2 ≤ 7*badPhaseCount good I; omega⟩
            | cons d tail =>
              have hd : good d = true := (List.all_eq_true.mp htail) d (by simp)
              cases tail with
              | nil =>
                exact ⟨.block q I c d .terminal,congrArg (List.cons q) hpart,⟨hq,hc,hd,True.intro⟩,⟨hsize,True.intro⟩⟩
              | cons e es =>
                have he : good e = true := (List.all_eq_true.mp htail) e (by simp)
                have hes : es.length < fuel := by simp only [List.length_cons] at hf hlen; omega
                obtain ⟨s,hph,hs,hcount⟩ := ih e es hes he
                refine ⟨.block q I c d s,?_,⟨hq,hc,hd,hs⟩,⟨hsize,hcount⟩⟩
                simpa only [InitialCutAssembly.phases,hph] using congrArg (List.cons q) hpart
  exact aux (qs.length+1) q qs (Nat.lt_succ_self _) hq

end
end StrongSilver
