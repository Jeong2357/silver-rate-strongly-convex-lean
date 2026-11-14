-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CutAssembly
import StrongSilver.ReservedRunCount

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 1800000

namespace CutAssembly

def Counted (good : CutPhase → Bool) : CutAssembly → Prop
  | .ordinaryEnd _ => True
  | .ordinary _ s => s.Counted good
  | .block _ I _ s => I.length+2 ≤ 4*badPhaseCount good I ∧ s.Counted good
  | .blockEnd _ I _ => I.length+2 ≤ 4*badPhaseCount good I
  | .noConnector _ I => I.length+1 ≤ 4*badPhaseCount good I

def blockCount : CutAssembly → ℕ
  | .ordinaryEnd _ => 0
  | .ordinary _ s => s.blockCount
  | .block _ _ _ s => 1+s.blockCount
  | .blockEnd _ _ _ => 1
  | .noConnector _ _ => 1

theorem blockCount_le_reserved (s : CutAssembly) : s.blockCount ≤ s.reserved.length := by
  induction s <;> simp_all [blockCount,reserved] <;> omega

theorem reserved_count_bound {good : CutPhase → Bool} {s : CutAssembly}
    (hs : s.WellFormed good) (hc : s.Counted good) : s.reserved.length ≤ 4*badPhaseCount good s.phases := by
  induction s with
  | ordinaryEnd q => simp [reserved]
  | ordinary q s ih =>
    have hh := ih hs.2 hc
    simpa only [reserved,phases,badPhaseCount_cons,hs.1,↓reduceIte,zero_add] using hh
  | block q I c s ih =>
    have hh := ih hs.2.2 hc.2
    have hsize := hc.1
    simp only [reserved,phases,List.length_cons,List.length_append,badPhaseCount_cons,
      badPhaseCount_append,hs.1,hs.2.1,↓reduceIte,zero_add]
    omega
  | blockEnd q I c =>
    have hq := hs.1
    have hright := hs.2
    change good q = true at hq
    change good c = true at hright
    change I.length+2 ≤ 4*badPhaseCount good I at hc
    simp only [reserved,phases,List.length_cons,List.length_append,List.length_singleton,
      badPhaseCount_append,badPhaseCount_cons,badPhaseCount_nil,hq,hright,↓reduceIte,zero_add,add_zero]
    omega
  | noConnector q I =>
    change good q = true at hs
    change I.length+1 ≤ 4*badPhaseCount good I at hc
    simpa [reserved,phases,badPhaseCount_cons,hs,Nat.add_comm] using hc

end CutAssembly

theorem buildCutAssembly_counted (good : CutPhase → Bool) (fuel : ℕ) :
    ∀ q qs s, buildCutAssembly good fuel q qs = some s → s.Counted good := by
  induction fuel with
  | zero => intro q qs s hs; simp [buildCutAssembly] at hs
  | succ fuel ih =>
    intro q qs s hs
    cases qs with
    | nil =>
      simp only [buildCutAssembly,Option.some.injEq] at hs
      cases hs
      trivial
    | cons r rs =>
      by_cases hr : good r = true
      · simp only [buildCutAssembly,hr,↓reduceIte] at hs
        cases hchild : buildCutAssembly good fuel r rs with
        | none => simp [hchild] at hs
        | some child =>
          simp only [hchild,Option.map_some,Option.some.injEq] at hs
          cases hs
          exact ih r rs child hchild
      · have hrfalse := Bool.eq_false_iff.mpr hr
        have hsize := reserveRun_one_reserved_size (qs := rs) hrfalse
        generalize hR : reserveRun good 1 (r::rs) = R
        rcases R with ⟨I,rem⟩
        rw [hR] at hsize
        cases rem with
        | nil =>
          simp only [buildCutAssembly,hr,↓reduceIte,hR,Option.some.injEq] at hs
          cases hs
          change I.length+1 ≤ 4*badPhaseCount good I
          change I.length+2 ≤ 4*badPhaseCount good I at hsize
          omega
        | cons c tail =>
          cases tail with
          | nil =>
            simp only [buildCutAssembly,hr,↓reduceIte,hR,Option.some.injEq] at hs
            cases hs
            exact hsize
          | cons d ds =>
            simp only [buildCutAssembly,hr,↓reduceIte,hR] at hs
            cases hchild : buildCutAssembly good fuel d ds with
            | none => simp [hchild] at hs
            | some child =>
              simp only [hchild,Option.map_some,Option.some.injEq] at hs
              cases hs
              exact ⟨hsize,ih d ds child hchild⟩

theorem exists_counted_cutAssembly (good : CutPhase → Bool) (q : CutPhase) (qs : List CutPhase)
    (hq : good q = true) : ∃ s : CutAssembly,
      s.phases = q::qs ∧ s.WellFormed good ∧ s.Counted good ∧ s.reserved.length ≤ 4*badPhaseCount good (q::qs) := by
  obtain ⟨s,hbuild,hph,hgood⟩ := buildCutAssembly_correct good (qs.length+1) q qs (Nat.lt_succ_self _) hq
  have hc := buildCutAssembly_counted good (qs.length+1) q qs s hbuild
  refine ⟨s,hph,hgood,hc,?_⟩
  simpa only [hph] using s.reserved_count_bound hgood hc

end
end StrongSilver
