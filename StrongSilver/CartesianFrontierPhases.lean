-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CartesianThresholdCut
import Mathlib.Data.List.Chain

namespace StrongSilver.ScheduleTree
noncomputable section
set_option maxHeartbeats 3000000

/-- Adaptive chronological frontier, with the actual following selected
pivot attached to each gap. The final entry keeps the exterior boundary. -/
def frontierPhases (A : ℝ) : ScheduleTree → ℝ → List (ScheduleTree × ℝ)
  | t@(.leaf _),b => [(t,b)]
  | t@(.split l p r),b => if A < p then frontierPhases A l p++frontierPhases A r b else [(t,b)]

def splitNodes : ScheduleTree → List ScheduleTree
  | .leaf _ => []
  | t@(.split l _ r) => t::(splitNodes l++splitNodes r)

theorem frontierPhases_nonempty (A : ℝ) (t : ScheduleTree) (b : ℝ) : frontierPhases A t b ≠ [] := by
  induction t generalizing b with
  | leaf h => simp [frontierPhases]
  | split l p r il ir =>
    unfold frontierPhases
    split_ifs with hp
    · intro h
      exact il p (List.append_eq_nil_iff.mp h).1
    · simp

theorem frontierPhases_map_fst (A : ℝ) (t : ScheduleTree) (b : ℝ) :
    (frontierPhases A t b).map Prod.fst = frontier A t := by
  induction t generalizing b with
  | leaf h => rfl
  | split l p r il ir =>
    simp only [frontierPhases,frontier]
    split_ifs with hp
    · simp only [List.map_append,il,ir]
    · rfl

theorem frontierPhases_word (A : ℝ) (t : ScheduleTree) (b : ℝ) :
    ((frontierPhases A t b).flatMap fun q => q.1.word++[q.2]) = t.word++[b] := by
  induction t generalizing b with
  | leaf h => simp [frontierPhases]
  | split l p r il ir =>
    simp only [frontierPhases]
    split_ifs with hp
    · simp only [List.flatMap_append,il,ir,word]
      simp [List.append_assoc]
    · simp

theorem frontierPhases_first_prefix (A : ℝ) (t : ScheduleTree) (b : ℝ) :
    ∀ q ∈ (frontierPhases A t b).head?, q.1.word.IsPrefix t.word := by
  induction t generalizing b with
  | leaf h => simp [frontierPhases]
  | split l p r il ir =>
    simp only [frontierPhases]
    split_ifs with hp
    · intro q hq
      rw [List.head?_append_of_ne_nil _ (frontierPhases_nonempty A l p)] at hq
      exact (il p q hq).trans ⟨p::r.word,rfl⟩
    · simp

theorem frontierPhases_last_suffix (A : ℝ) (t : ScheduleTree) (b : ℝ) :
    ∀ q ∈ (frontierPhases A t b).getLast?, q.2 = b ∧ q.1.word.IsSuffix t.word := by
  induction t generalizing b with
  | leaf h => simp [frontierPhases]
  | split l p r il ir =>
    simp only [frontierPhases]
    split_ifs with hp
    · intro q hq
      rw [List.getLast?_append_of_ne_nil _ (frontierPhases_nonempty A r b)] at hq
      obtain ⟨hb,hs⟩ := ir b q hq
      refine ⟨hb,hs.trans ?_⟩
      exact ⟨l.word++[p],by simp [word,List.append_assoc]⟩
    · simp

end
end StrongSilver.ScheduleTree
