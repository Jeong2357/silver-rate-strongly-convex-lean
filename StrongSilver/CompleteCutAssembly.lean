-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CutAssemblyCount

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 1800000

/-- A block at the first step has no left attachment. -/
inductive CompleteCutAssembly where
  | scalar (inside : List CutPhase)
  | positive (suffix : CutAssembly)
  | leadingBlock (inside : List CutPhase) (right : CutPhase) (suffix : CutAssembly)
  | leadingEnd (inside : List CutPhase) (right : CutPhase)

namespace CompleteCutAssembly

def phases : CompleteCutAssembly → List CutPhase
  | .scalar I => I
  | .positive s => s.phases
  | .leadingBlock I c s => I++(c::s.phases)
  | .leadingEnd I c => I++[c]

def tracked : CompleteCutAssembly → List CutPhase
  | .scalar _ => []
  | .positive s => s.tracked
  | .leadingBlock _ _ s => s.tracked
  | .leadingEnd _ _ => []

def reserved : CompleteCutAssembly → List CutPhase
  | .scalar I => I
  | .positive s => s.reserved
  | .leadingBlock I c s => I++(c::s.reserved)
  | .leadingEnd I c => I++[c]

def WellFormed (good : CutPhase → Bool) : CompleteCutAssembly → Prop
  | .scalar _ => True
  | .positive s => s.WellFormed good
  | .leadingBlock _ c s => good c = true ∧ s.WellFormed good
  | .leadingEnd _ c => good c = true

def Counted (good : CutPhase → Bool) : CompleteCutAssembly → Prop
  | .scalar I => I.length ≤ 4*badPhaseCount good I
  | .positive s => s.Counted good
  | .leadingBlock I _ s => I.length+1 ≤ 4*badPhaseCount good I ∧ s.Counted good
  | .leadingEnd I _ => I.length+1 ≤ 4*badPhaseCount good I

theorem length_partition (s : CompleteCutAssembly) : s.phases.length = s.tracked.length+s.reserved.length := by
  cases s <;> simp_all [phases,tracked,reserved,CutAssembly.length_partition] <;> omega

theorem reserved_count_bound {good : CutPhase → Bool} {s : CompleteCutAssembly}
    (hs : s.WellFormed good) (hc : s.Counted good) : s.reserved.length ≤ 4*badPhaseCount good s.phases := by
  cases s with
  | scalar I => exact hc
  | positive s => exact s.reserved_count_bound hs hc
  | leadingBlock I c s =>
    have hh := s.reserved_count_bound hs.2 hc.2
    have hsize := hc.1
    simp only [reserved,phases,List.length_append,List.length_cons,badPhaseCount_append,
      badPhaseCount_cons,hs.1,↓reduceIte,zero_add]
    omega
  | leadingEnd I c =>
    change good c = true at hs
    change I.length+1 ≤ 4*badPhaseCount good I at hc
    simpa [reserved,phases,badPhaseCount_append,badPhaseCount_cons,hs,Nat.add_comm] using hc

end CompleteCutAssembly

/-- The reservation algorithm is defined for every finite list of phases,
including a marked first phase and the empty cut. -/
theorem exists_complete_cutAssembly (good : CutPhase → Bool) (qs : List CutPhase) :
    ∃ s : CompleteCutAssembly, s.phases = qs ∧ s.WellFormed good ∧ s.Counted good ∧
      s.reserved.length ≤ 4*badPhaseCount good qs := by
  cases qs with
  | nil => exact ⟨.scalar [],rfl,True.intro,by simp [CompleteCutAssembly.Counted],by simp [CompleteCutAssembly.reserved]⟩
  | cons q qs =>
    by_cases hq : good q = true
    · obtain ⟨s,hph,hs,hc,hcount⟩ := exists_counted_cutAssembly good q qs hq
      exact ⟨.positive s,hph,hs,hc,hcount⟩
    · have hqfalse := Bool.eq_false_iff.mpr hq
      have hsize := reserveRun_one_reserved_size (qs := qs) hqfalse
      generalize hR : reserveRun good 1 (q::qs) = R
      rcases R with ⟨I,rem⟩
      rw [hR] at hsize
      change I.length+2 ≤ 4*badPhaseCount good I at hsize
      have hpart := ReservedRun.partition good 1 (q::qs)
      rw [hR] at hpart
      have hg := ReservedRun.remaining_good good 1 (q::qs)
      rw [hR] at hg
      suffices h : ∃ s : CompleteCutAssembly, s.phases = q::qs ∧ s.WellFormed good ∧ s.Counted good by
        obtain ⟨s,hph,hs,hc⟩ := h
        exact ⟨s,hph,hs,hc,by simpa only [hph] using s.reserved_count_bound hs hc⟩
      cases rem with
      | nil =>
        refine ⟨.scalar I,?_,True.intro,?_⟩
        · simpa only [CompleteCutAssembly.phases,List.append_nil] using hpart
        · change I.length ≤ 4*badPhaseCount good I
          omega
      | cons c tail =>
        obtain ⟨hc,htail⟩ := hg c tail rfl
        cases tail with
        | nil =>
          exact ⟨.leadingEnd I c,hpart,hc,by change I.length+1 ≤ 4*badPhaseCount good I; omega⟩
        | cons d ds =>
          have hd : good d = true := by simpa only [List.take_succ_cons,List.take_zero,List.all_cons,List.all_nil,Bool.and_true] using htail
          obtain ⟨s,hph,hs,hcount,_⟩ := exists_counted_cutAssembly good d ds hd
          refine ⟨.leadingBlock I c s,?_,⟨hc,hs⟩,?_,hcount⟩
          · simpa only [CompleteCutAssembly.phases,hph] using hpart
          · change I.length+1 ≤ 4*badPhaseCount good I
            omega

end
end StrongSilver
