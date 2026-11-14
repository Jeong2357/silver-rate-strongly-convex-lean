-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.LinkedFrontier
import StrongSilver.FiniteBooleanEvaluation

namespace StrongSilver.ScheduleTree
open BinaryForest
noncomputable section
set_option maxHeartbeats 5400000

/-- A frontier determined by one finite Boolean mask on the original
indexed internal vertices. -/
def maskedLinkedFrontier (start : ℕ) (κ : ℝ) (parent following : Option ScheduleNode) :
    ScheduleTree → List Bool → List LinkedGap
  | t@(.leaf _), _ => [⟨⟨start,t,κ⟩,parent,following⟩]
  | t@(.split l _ r), mask =>
    let q : ScheduleNode := ⟨start,t,κ⟩
    if mask.headD false then maskedLinkedFrontier start 0 (some q) (some q) l (mask.tail.take l.nodeCount)++
      maskedLinkedFrontier (start+l.word.length+1) κ (some q) following r (mask.tail.drop l.nodeCount)
    else [⟨q,parent,following⟩]

/-- The actual cutoff frontier depends on exactly the finite original
pivot decisions; arbitrary gap observables can therefore be integrated
without a measurable structure on the gap metadata. -/
theorem maskedLinkedFrontier_actual (φ : ℝ → ℝ) (s : ℝ) (start : ℕ) (κ : ℝ)
    (parent following : Option ScheduleNode) (t : ScheduleTree) :
    maskedLinkedFrontier start κ parent following t
      ((labels (t.indexedTree start κ)).map fun q => decide (s < φ q.pivot)) =
      linkedFrontier φ s start κ parent following t := by
  induction t generalizing start κ parent following with
  | leaf word => rfl
  | split l b r il ir =>
    have hLlen : (((labels (l.indexedTree start 0)).map fun q => decide (s < φ q.pivot)).length) = l.nodeCount := by
      rw [List.length_map,labels_length,indexedTree_numNodes]
    simp only [indexedTree,labels,List.map_cons,List.map_append,maskedLinkedFrontier,List.headD_cons,List.tail_cons]
    rw [List.take_left' hLlen,List.drop_left' hLlen,il,ir]
    simp only [ScheduleNode.pivot,rootStep_split,linkedFrontier]
    by_cases hb : s < φ b <;> simp [hb]

end
end StrongSilver.ScheduleTree
