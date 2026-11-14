-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ReservedTreeNodes
import Mathlib.Data.Tree.Basic

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 2800000

/-- One occurrence of an original Cartesian interval, with its actual
starting position and terminal reserve. Equal-valued intervals at
different positions have separate labels. -/
structure ScheduleNode where
  start : ℕ
  source : ScheduleTree
  reserve : ℝ

namespace ScheduleNode

def pivotIndex (q : ScheduleNode) : ℕ :=
  match q.source with
  | .leaf _ => q.start
  | .split l _ _ => q.start+l.word.length

def pivot (q : ScheduleNode) : ℝ := q.source.rootStep

end ScheduleNode

namespace BinaryForest

def labels {α : Type*} : BinaryTree α → List α
  | .nil => []
  | .node v l r => v::(labels l++labels r)

theorem labels_length {α : Type*} (t : BinaryTree α) : (labels t).length = t.numNodes := by
  induction t with
  | nil => rfl
  | node v l r il ir => simp only [labels,List.length_cons,List.length_append,BinaryTree.numNodes,il,ir]

end BinaryForest

namespace ScheduleTree

def indexedTree (start : ℕ) (κ : ℝ) : ScheduleTree → BinaryTree ScheduleNode
  | .leaf _ => .nil
  | t@(.split l _ r) => .node ⟨start,t,κ⟩ (indexedTree start 0 l) (indexedTree (start+l.word.length+1) κ r)

theorem indexedTree_numNodes (start : ℕ) (κ : ℝ) (t : ScheduleTree) : (t.indexedTree start κ).numNodes = t.nodeCount := by
  induction t generalizing start κ with
  | leaf hw => rfl
  | split l b r il ir => simp only [indexedTree,BinaryTree.numNodes,nodeCount,il,ir]; omega

/-- Erasing only the positions gives precisely the existing reserve
list used by the exact cut and excess identities. -/
theorem indexedTree_labels_reserves (start : ℕ) (κ : ℝ) (t : ScheduleTree) :
    ((BinaryForest.labels (t.indexedTree start κ)).map fun q => (q.source,q.reserve)) = t.reservedNodes κ := by
  induction t generalizing start κ with
  | leaf hw => rfl
  | split l b r il ir => simp only [indexedTree,BinaryForest.labels,List.map_cons,List.map_append,reservedNodes,il,ir]

theorem indexedTree_pivot_bounds {start : ℕ} {κ : ℝ} {t : ScheduleTree} {q : ScheduleNode}
    (hq : q ∈ BinaryForest.labels (t.indexedTree start κ)) : start ≤ q.pivotIndex ∧ q.pivotIndex < start+t.word.length := by
  induction t generalizing start κ with
  | leaf hw => simp [indexedTree,BinaryForest.labels] at hq
  | split l b r il ir =>
    simp only [indexedTree,BinaryForest.labels,List.mem_cons,List.mem_append] at hq
    rcases hq with rfl | hq | hq
    · simp only [ScheduleNode.pivotIndex,word,List.length_append,List.length_cons]
      omega
    · have hh := il hq
      simp only [word,List.length_append,List.length_cons]
      omega
    · have hh := ir hq
      simp only [word,List.length_append,List.length_cons]
      omega

end ScheduleTree
end
end StrongSilver
