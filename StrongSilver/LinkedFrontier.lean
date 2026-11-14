-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ParentedScheduleNodes
import StrongSilver.CartesianFrontierPhases

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 5400000

/-- An original chronological gap, together with its immediate
Cartesian parent and its following selected pivot, all position-labeled. -/
structure LinkedGap where
  node : ScheduleNode
  parent : Option ScheduleNode
  following : Option ScheduleNode

namespace LinkedGap

def toParented (q : LinkedGap) : ParentedScheduleNode := ⟨q.node,q.parent⟩
def followingStep (fallback : ℝ) (q : LinkedGap) : ℝ := (q.following.map ScheduleNode.pivot).getD fallback
end LinkedGap

namespace ScheduleTree

def linkedFrontier (φ : ℝ → ℝ) (s : ℝ) (start : ℕ) (κ : ℝ)
    (parent following : Option ScheduleNode) : ScheduleTree → List LinkedGap
  | t@(.leaf _) => [⟨⟨start,t,κ⟩,parent,following⟩]
  | t@(.split l b r) =>
    let q : ScheduleNode := ⟨start,t,κ⟩
    if s < φ b then linkedFrontier φ s start 0 (some q) (some q) l++
      linkedFrontier φ s (start+l.word.length+1) κ (some q) following r
    else [⟨q,parent,following⟩]

theorem linkedFrontier_erase (φ : ℝ → ℝ) (s : ℝ) (start : ℕ) (κ : ℝ)
    (parent following : Option ScheduleNode) (t : ScheduleTree) :
    ((linkedFrontier φ s start κ parent following t).map LinkedGap.node) = indexedFrontier φ s start κ t := by
  induction t generalizing start κ parent following with
  | leaf hw => rfl
  | split l b r il ir =>
    simp only [linkedFrontier,indexedFrontier]
    split_ifs <;> simp only [List.map_append,il,ir,List.map_cons,List.map_nil]

theorem linkedFrontier_nonempty (φ : ℝ → ℝ) (s : ℝ) (start : ℕ) (κ : ℝ)
    (parent following : Option ScheduleNode) (t : ScheduleTree) : linkedFrontier φ s start κ parent following t ≠ [] := by
  induction t generalizing start κ parent following with
  | leaf hw => simp [linkedFrontier]
  | split l b r il ir =>
    simp only [linkedFrontier]
    split_ifs
    · intro hh
      exact il _ _ _ _ (List.append_eq_nil_iff.mp hh).1
    · simp

/-- The following labels give the same chronological phases as the
original Cartesian frontier, including its exterior terminal boundary. -/
theorem linkedFrontier_phases (φ : ℝ → ℝ) (s A fallback : ℝ)
    (hcut : ∀ b, s < φ b ↔ A < b) (start : ℕ) (κ : ℝ)
    (parent following : Option ScheduleNode) (t : ScheduleTree) :
    ((linkedFrontier φ s start κ parent following t).map fun q => (q.node.source,q.followingStep fallback)) =
      frontierPhases A t ((following.map ScheduleNode.pivot).getD fallback) := by
  induction t generalizing start κ parent following with
  | leaf hw => rfl
  | split l b r il ir =>
    simp only [linkedFrontier,frontierPhases,← hcut b]
    split_ifs
    · simp only [List.map_append,il,ir,Option.map_some,Option.getD_some,ScheduleNode.pivot,rootStep_split]
    · rfl

/-- An internal linked gap has its actual parented occurrence and is
visible at the cut. Equality of lists preserves multiplicity. -/
theorem linkedFrontier_internal_parented (φ : ℝ → ℝ) (hφ : Monotone φ) (s : ℝ)
    (start : ℕ) (κ : ℝ) (parent following : Option ScheduleNode) (t : ScheduleTree)
    (hc : t.Cartesian) (hp : ParentedScheduleNode.parentAbove φ s parent) :
    (((linkedFrontier φ s start κ parent following t).filter fun q => internalNode q.node).map LinkedGap.toParented) =
      ((parentedNodes start κ parent t).filter fun q => @decide (q.Visible φ s) (Classical.propDecidable _)) := by
  classical
  induction t generalizing start κ parent following with
  | leaf hw => simp [linkedFrontier,internalNode,parentedNodes]
  | split l b r il ir =>
    by_cases hb : s < φ b
    · have hn : ¬ (⟨⟨start,.split l b r,κ⟩,parent⟩ : ParentedScheduleNode).Visible φ s := fun hh => not_le_of_gt hb hh.1
      have hnew : ParentedScheduleNode.parentAbove φ s (some (⟨start,.split l b r,κ⟩ : ScheduleNode)) := hb
      simp only [linkedFrontier,if_pos hb,List.filter_append,List.map_append,il _ _ _ _ hc.1 hnew,ir _ _ _ _ hc.2.1 hnew,
        parentedNodes,List.filter_cons,decide_eq_false hn,Bool.false_eq_true,↓reduceIte,List.filter_append]
    · have hv : (⟨⟨start,.split l b r,κ⟩,parent⟩ : ParentedScheduleNode).Visible φ s := ⟨le_of_not_gt hb,hp⟩
      have hnew : ¬ ParentedScheduleNode.parentAbove φ s (some (⟨start,.split l b r,κ⟩ : ScheduleNode)) := hb
      have hl : ∀ x ∈ l.word, φ x ≤ s := fun x hx =>
        (hφ ((hc.2.2.2.1 x hx).le)).trans (le_of_not_gt hb)
      have hr : ∀ x ∈ r.word, φ x ≤ s := fun x hx =>
        (hφ (hc.2.2.2.2 x hx)).trans (le_of_not_gt hb)
      simp only [linkedFrontier,if_neg hb,List.filter_cons,internalNode,↓reduceIte,List.filter_nil,List.map_cons,List.map_nil,
        parentedNodes,decide_eq_true hv,List.filter_append,
        parentedNodes_invisible φ hφ s start 0 _ l hc.1 hl hnew,
        parentedNodes_invisible φ hφ s _ κ _ r hc.2.1 hr hnew,List.nil_append,LinkedGap.toParented]

end ScheduleTree
end
end StrongSilver
