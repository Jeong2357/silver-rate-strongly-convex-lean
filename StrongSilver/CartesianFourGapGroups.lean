-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CartesianDepthPhases
import StrongSilver.FourPhaseWords

namespace StrongSilver.ScheduleTree
noncomputable section
set_option maxHeartbeats 2000000

structure FourGapGroup where
  first : ScheduleTree
  second : ScheduleTree
  third : ScheduleTree
  fourth : ScheduleTree
  leftPivot : ℝ
  middlePivot : ℝ
  rightPivot : ℝ

namespace FourGapGroup

def left (G : FourGapGroup) : ScheduleTree := .split G.first G.leftPivot G.second
def right (G : FourGapGroup) : ScheduleTree := .split G.third G.rightPivot G.fourth
def tree (G : FourGapGroup) : ScheduleTree := .split G.left G.middlePivot G.right

def gaps (G : FourGapGroup) : Fin 4 → List ℝ := ![G.first.word,G.second.word,G.third.word,G.fourth.word]
def pivots (G : FourGapGroup) (b : ℝ) : Fin 4 → ℝ := ![G.leftPivot,G.middlePivot,G.rightPivot,b]

theorem original_word (G : FourGapGroup) (b : ℝ) : G.tree.word++[b] =
    FourPhase.phaseWord G.gaps (G.pivots b) 0++FourPhase.phaseWord G.gaps (G.pivots b) 1++
    FourPhase.phaseWord G.gaps (G.pivots b) 2++FourPhase.phaseWord G.gaps (G.pivots b) 3 := by
  change (G.first.word++G.leftPivot::G.second.word++G.middlePivot::(G.third.word++G.rightPivot::G.fourth.word))++[b] =
    (G.first.word++[G.leftPivot])++(G.second.word++[G.middlePivot])++
    (G.third.word++[G.rightPivot])++(G.fourth.word++[b])
  simp only [List.append_assoc,List.cons_append,List.singleton_append,List.nil_append]

end FourGapGroup

def completeThrough : ℕ → ScheduleTree → Prop
  | 0,_ => True
  | _+1,.leaf _ => False
  | d+1,.split l _ r => completeThrough d l ∧ completeThrough d r

theorem exists_fourGapGroup {t : ScheduleTree} (hc : completeThrough 2 t) : ∃ G : FourGapGroup, G.tree = t := by
  cases t with
  | leaf h => exact False.elim hc
  | split l p r =>
    cases l with
    | leaf h => exact False.elim hc.1
    | split ll lp lr =>
      cases r with
      | leaf h => exact False.elim hc.2
      | split rl rp rr => exact ⟨⟨ll,lr,rl,rr,lp,p,rp⟩,rfl⟩

theorem complete_frontier {d k : ℕ} {t : ScheduleTree} (hc : completeThrough (d+k) t)
    {s : ScheduleTree} (hs : s ∈ depthFrontier d t) : completeThrough k s := by
  induction d generalizing t with
  | zero =>
    simp only [depthFrontier,List.mem_singleton] at hs
    subst s
    simpa only [Nat.zero_add] using hc
  | succ d ih =>
    cases t with
    | leaf h =>
      have hfalse : False := by simpa only [Nat.succ_add,completeThrough] using hc
      exact False.elim hfalse
    | split l p r =>
      have hchildren : completeThrough (d+k) l ∧ completeThrough (d+k) r := by
        simpa only [Nat.succ_add,completeThrough] using hc
      simp only [depthFrontier,List.mem_append] at hs
      rcases hs with hs | hs
      · exact ih hchildren.1 hs
      · exact ih hchildren.2 hs

/-- Every group in the chronological depth frontier is an actual
four-gap block when the required two generations of roots exist. -/
theorem depth_group_decomposition {d : ℕ} {t : ScheduleTree} (hc : completeThrough (d+2) t)
    {s : ScheduleTree} (hs : s ∈ depthFrontier d t) : ∃ G : FourGapGroup, G.tree = s :=
  exists_fourGapGroup (complete_frontier hc hs)

end
end StrongSilver.ScheduleTree
