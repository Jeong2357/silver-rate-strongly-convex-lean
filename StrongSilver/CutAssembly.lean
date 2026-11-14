-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.WorkingAssembly
import StrongSilver.ReservedRun

namespace StrongSilver
noncomputable section

/-- A cut partition records the phases traversed inside each exceptional
block, as well as its separate left attachment and right connector. -/
inductive CutAssembly where
  | ordinaryEnd (q : CutPhase)
  | ordinary (q : CutPhase) (suffix : CutAssembly)
  | block (left : CutPhase) (inside : List CutPhase) (right : CutPhase) (suffix : CutAssembly)
  | blockEnd (left : CutPhase) (inside : List CutPhase) (right : CutPhase)
  | noConnector (left : CutPhase) (inside : List CutPhase)

namespace CutAssembly

def phases : CutAssembly → List CutPhase
  | .ordinaryEnd q => [q]
  | .ordinary q s => q :: s.phases
  | .block q I c s => q :: (I ++ (c :: s.phases))
  | .blockEnd q I c => q :: (I ++ [c])
  | .noConnector q I => q :: I

def WellFormed (good : CutPhase → Bool) : CutAssembly → Prop
  | .ordinaryEnd q => good q = true
  | .ordinary q s => good q = true ∧ s.WellFormed good
  | .block q _ c s => good q = true ∧ good c = true ∧ s.WellFormed good
  | .blockEnd q _ c => good q = true ∧ good c = true
  | .noConnector q _ => good q = true

def erase (t : List ℝ) : CutAssembly → WorkingAssembly
  | .ordinaryEnd q => .ordinaryEnd q t
  | .ordinary q s => .ordinary q (s.erase t)
  | .block q I c s => .block q (I.flatMap CutPhase.word++c.gap) c.pivot (s.erase t)
  | .blockEnd q I c => .blockEnd q (I.flatMap CutPhase.word++c.gap) c.pivot t
  | .noConnector q I => .noConnector q (I.flatMap CutPhase.word) t

theorem erase_word (s : CutAssembly) (t : List ℝ) :
    (s.erase t).word = s.phases.flatMap CutPhase.word++t := by
  induction s <;> simp_all [erase,WorkingAssembly.word,phases,CutPhase.word,List.append_assoc]

def tracked : CutAssembly → List CutPhase
  | .ordinaryEnd q => [q]
  | .ordinary q s => q :: s.tracked
  | .block _ _ _ s => s.tracked
  | .blockEnd _ _ _ => []
  | .noConnector _ _ => []

def reserved : CutAssembly → List CutPhase
  | .ordinaryEnd _ => []
  | .ordinary _ s => s.reserved
  | .block q I c s => q :: (I ++ (c :: s.reserved))
  | .blockEnd q I c => q :: (I ++ [c])
  | .noConnector q I => q :: I

theorem erase_tracked (s : CutAssembly) (t : List ℝ) : (s.erase t).tracked = s.tracked := by
  induction s <;> simp_all [erase,WorkingAssembly.tracked,tracked]

theorem length_partition (s : CutAssembly) : s.phases.length = s.tracked.length+s.reserved.length := by
  induction s <;> simp_all [phases,tracked,reserved] <;> omega

end CutAssembly

/-- One good phase is left between separate connecting roles. Two good
phases stop the block scan; the right one starts the next recursive assembly. -/
def buildCutAssembly (good : CutPhase → Bool) : ℕ → CutPhase → List CutPhase → Option CutAssembly
  | 0, _, _ => none
  | fuel+1, q, [] => some (.ordinaryEnd q)
  | fuel+1, q, r::rs =>
    if good r then (buildCutAssembly good fuel r rs).map (.ordinary q)
    else
      let R := reserveRun good 1 (r::rs)
      match R.remaining with
      | [] => some (.noConnector q R.inside)
      | c::[] => some (.blockEnd q R.inside c)
      | c::d::ds => (buildCutAssembly good fuel d ds).map (.block q R.inside c)

theorem buildCutAssembly_correct (good : CutPhase → Bool) (fuel : ℕ) :
    ∀ q qs, qs.length < fuel → good q = true →
      ∃ s : CutAssembly, buildCutAssembly good fuel q qs = some s ∧
        s.phases = q::qs ∧ s.WellFormed good := by
  induction fuel with
  | zero => intro q qs hf; omega
  | succ fuel ih =>
    intro q qs hf hq
    cases qs with
    | nil => exact ⟨.ordinaryEnd q,rfl,rfl,hq⟩
    | cons r rs =>
      by_cases hr : good r = true
      · obtain ⟨s,hs,hph,hgood⟩ := ih r rs (by simp only [List.length_cons] at hf; omega) hr
        refine ⟨.ordinary q s,?_,?_,hq,hgood⟩
        · simp [buildCutAssembly,hr,hs]
        · simp only [CutAssembly.phases,hph]
      · have hrfalse : good r = false := Bool.eq_false_iff.mpr hr
        generalize hR : reserveRun good 1 (r::rs) = R
        rcases R with ⟨I,rem⟩
        have hpart := ReservedRun.partition good 1 (r::rs)
        rw [hR] at hpart
        have hlen := ReservedRun.remaining_length_le good 1 (r::rs)
        rw [hR] at hlen
        have hg := ReservedRun.remaining_good good 1 (r::rs)
        rw [hR] at hg
        cases rem with
        | nil =>
          refine ⟨.noConnector q I,?_,?_,hq⟩
          · simp [buildCutAssembly,hr,hR]
          · simpa only [CutAssembly.phases,List.append_nil] using congrArg (List.cons q) hpart
        | cons c tail =>
          obtain ⟨hc,htail⟩ := hg c tail rfl
          cases tail with
          | nil =>
            refine ⟨.blockEnd q I c,?_,?_,hq,hc⟩
            · simp [buildCutAssembly,hr,hR]
            · exact congrArg (List.cons q) hpart
          | cons d ds =>
            have hd : good d = true := by simpa only [List.take_succ_cons,List.take_zero,List.all_cons,List.all_nil,Bool.and_true] using htail
            have hds : ds.length < fuel := by
              simp only [List.length_cons] at hf hlen
              omega
            obtain ⟨s,hs,hph,hgood⟩ := ih d ds hds hd
            refine ⟨.block q I c s,?_,?_,hq,hc,hgood⟩
            · simp [buildCutAssembly,hr,hR,hs]
            · simpa only [CutAssembly.phases,hph] using congrArg (List.cons q) hpart

theorem exists_cutAssembly (good : CutPhase → Bool) (q : CutPhase) (qs : List CutPhase)
    (hq : good q = true) : ∃ s : CutAssembly, s.phases = q::qs ∧ s.WellFormed good := by
  obtain ⟨s,_,hph,hgood⟩ := buildCutAssembly_correct good (qs.length+1) q qs (Nat.lt_succ_self _) hq
  exact ⟨s,hph,hgood⟩

end
end StrongSilver
