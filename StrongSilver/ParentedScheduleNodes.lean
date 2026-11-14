-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.IndexedFrontier

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 3600000

structure ParentedScheduleNode where
  node : ScheduleNode
  parent : Option ScheduleNode

namespace ParentedScheduleNode

def parentAbove (φ : ℝ → ℝ) (s : ℝ) : Option ScheduleNode → Prop
  | none => True
  | some q => s < φ q.pivot

def Visible (φ : ℝ → ℝ) (s : ℝ) (q : ParentedScheduleNode) : Prop :=
  φ q.node.pivot ≤ s ∧ parentAbove φ s q.parent

end ParentedScheduleNode

namespace ScheduleTree
open ParentedScheduleNode

def parentedNodes (start : ℕ) (κ : ℝ) (parent : Option ScheduleNode) : ScheduleTree → List ParentedScheduleNode
  | .leaf _ => []
  | t@(.split l _ r) =>
    let q : ScheduleNode := ⟨start,t,κ⟩
    ⟨q,parent⟩::(parentedNodes start 0 (some q) l++parentedNodes (start+l.word.length+1) κ (some q) r)

theorem parentedNodes_erase (start : ℕ) (κ : ℝ) (parent : Option ScheduleNode) (t : ScheduleTree) :
    ((parentedNodes start κ parent t).map ParentedScheduleNode.node) = BinaryForest.labels (t.indexedTree start κ) := by
  induction t generalizing start κ parent with
  | leaf hw => rfl
  | split l b r il ir => simp only [parentedNodes,indexedTree,BinaryForest.labels,List.map_cons,List.map_append,il,ir]

def internalNode (q : ScheduleNode) : Bool :=
  match q.source with
  | .leaf _ => false
  | .split _ _ _ => true

local instance (φ : ℝ → ℝ) (s : ℝ) (q : ParentedScheduleNode) : Decidable (q.Visible φ s) := Classical.propDecidable _

/-- Below a nonselected parent every descendant is hidden. This uses
actual Cartesian pivot order and retains all node occurrences. -/
theorem parentedNodes_invisible (φ : ℝ → ℝ) (hφ : Monotone φ) (s : ℝ)
    (start : ℕ) (κ : ℝ) (parent : Option ScheduleNode) (t : ScheduleTree) (hc : t.Cartesian)
    (hword : ∀ b ∈ t.word, φ b ≤ s) (hp : ¬ parentAbove φ s parent) :
    ((parentedNodes start κ parent t).filter fun q => decide (q.Visible φ s)) = [] := by
  induction t generalizing start κ parent with
  | leaf hw => rfl
  | split l b r il ir =>
    have hb : φ b ≤ s := hword b (List.mem_append_right _ (by simp))
    have hparent : ¬ parentAbove φ s (some (⟨start,.split l b r,κ⟩ : ScheduleNode)) := not_lt_of_ge hb
    have hl : ∀ x ∈ l.word, φ x ≤ s := fun x hx => hword x (left_word_sublist l r b |>.subset hx)
    have hr : ∀ x ∈ r.word, φ x ≤ s := fun x hx => hword x (right_word_sublist l r b |>.subset hx)
    have hroot : ¬ (⟨⟨start,.split l b r,κ⟩,parent⟩ : ParentedScheduleNode).Visible φ s := fun hh => hp hh.2
    simp only [parentedNodes,List.filter_cons,decide_eq_false hroot,Bool.false_eq_true,↓reduceIte,List.filter_append,
      il start 0 _ hc.1 hl hparent,ir _ κ _ hc.2.1 hr hparent,List.nil_append]

/-- Visibility at a cutoff is exactly membership among the internal
roots of the positioned frontier gaps. The root has no upper boundary. -/
theorem parentedNodes_visible (φ : ℝ → ℝ) (hφ : Monotone φ) (s : ℝ)
    (start : ℕ) (κ : ℝ) (parent : Option ScheduleNode) (t : ScheduleTree) (hc : t.Cartesian)
    (hp : parentAbove φ s parent) :
    (((parentedNodes start κ parent t).filter fun q => decide (q.Visible φ s)).map ParentedScheduleNode.node) =
      (indexedFrontier φ s start κ t).filter internalNode := by
  induction t generalizing start κ parent with
  | leaf hw => simp [parentedNodes,indexedFrontier,internalNode]
  | split l b r il ir =>
    by_cases hb : s < φ b
    · have hn : ¬ (⟨⟨start,.split l b r,κ⟩,parent⟩ : ParentedScheduleNode).Visible φ s := fun hh => not_le_of_gt hb hh.1
      have hnew : parentAbove φ s (some (⟨start,.split l b r,κ⟩ : ScheduleNode)) := hb
      simp only [parentedNodes,List.filter_cons,decide_eq_false hn,Bool.false_eq_true,↓reduceIte,List.filter_append,
        List.map_append,il start 0 _ hc.1 hnew,ir _ κ _ hc.2.1 hnew,indexedFrontier,if_pos hb,List.filter_append]
    · have hv : (⟨⟨start,.split l b r,κ⟩,parent⟩ : ParentedScheduleNode).Visible φ s := ⟨le_of_not_gt hb,hp⟩
      have hnew : ¬ parentAbove φ s (some (⟨start,.split l b r,κ⟩ : ScheduleNode)) := hb
      have hl : ∀ x ∈ l.word, φ x ≤ s := fun x hx =>
        (hφ ((hc.2.2.2.1 x hx).le)).trans (le_of_not_gt hb)
      have hr : ∀ x ∈ r.word, φ x ≤ s := fun x hx =>
        (hφ (hc.2.2.2.2 x hx)).trans (le_of_not_gt hb)
      rw [parentedNodes,List.filter_cons]
      simp only [decide_eq_true hv,↓reduceIte,List.filter_append,
        parentedNodes_invisible φ hφ s start 0 _ l hc.1 hl hnew,
        parentedNodes_invisible φ hφ s _ κ _ r hc.2.1 hr hnew,List.nil_append,List.map_cons,List.map_nil,
        indexedFrontier,if_neg hb,List.filter_cons,internalNode,↓reduceIte,List.filter_nil]

end ScheduleTree
end
end StrongSilver
