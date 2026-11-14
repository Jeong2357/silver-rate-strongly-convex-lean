-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ActualScheduleEdges

namespace StrongSilver
open ScheduleTree
noncomputable section
set_option maxHeartbeats 5200000

def HasInternalRoot (t : ScheduleTree) : Prop := ∃ l r : ScheduleTree, ∃ b : ℝ, t = .split l b r

def AllGoodChildrenInternal (G : ScheduleNode → Bool) (start : ℕ) (κ : ℝ) : ScheduleTree → Prop
  | .leaf _ => True
  | t@(.split l _ r) =>
    (G ⟨start,t,κ⟩ = true → HasInternalRoot l ∧ HasInternalRoot r) ∧
      AllGoodChildrenInternal G start 0 l ∧ AllGoodChildrenInternal G (start+l.word.length+1) κ r

def missingGoodChildWeight (G : ScheduleNode → Bool) (w : ScheduleNode → ℝ) (q : ScheduleNode) : ℝ :=
  match q.source with
  | .leaf _ => 0
  | .split l _ r =>
    if G q = true ∧ ¬ (G ⟨q.start,l,0⟩ = true ∧ G ⟨q.start+l.word.length+1,r,q.reserve⟩ = true) then w q else 0

def badChildEdgeWeight (G : ScheduleNode → Bool) (w : ScheduleNode → ℝ) (q : ParentedScheduleNode) : ℝ :=
  match q.parent with
  | none => 0
  | some p => if G p = true ∧ G q.node ≠ true then w p else 0

def rootBadEdgeWeight (G : ScheduleNode → Bool) (w : ScheduleNode → ℝ) (start : ℕ) (κ : ℝ)
    (parent : Option ScheduleNode) : ScheduleTree → ℝ
  | .leaf _ => 0
  | t@(.split _ _ _) => match parent with
    | none => 0
    | some p => if G p = true ∧ G ⟨start,t,κ⟩ ≠ true then w p else 0

/-- A property checked on each original indexed occurrence gives the
recursive internal-child property. -/
theorem allGoodChildrenInternal_of_labels (G : ScheduleNode → Bool)
    (start : ℕ) (κ : ℝ) (t : ScheduleTree)
    (H : ∀ q ∈ BinaryForest.labels (t.indexedTree start κ), G q = true →
      match q.source with
      | .leaf _ => True
      | .split l _ r => HasInternalRoot l ∧ HasInternalRoot r) :
    AllGoodChildrenInternal G start κ t := by
  induction t generalizing start κ with
  | leaf hw => trivial
  | split l b r il ir =>
    refine ⟨?_,?_,?_⟩
    · exact H ⟨start,.split l b r,κ⟩ (by simp [indexedTree,BinaryForest.labels])
    · apply il start 0
      intro q hq
      exact H q (by simp only [indexedTree,BinaryForest.labels,List.mem_cons,List.mem_append]; exact Or.inr (Or.inl hq))
    · apply ir (start+l.word.length+1) κ
      intro q hq
      exact H q (by simp only [indexedTree,BinaryForest.labels,List.mem_cons,List.mem_append]; exact Or.inr (Or.inr hq))

/-- A good internal parent with a bad child can be paid by its actual
bad child edges. A parent with two bad children may be charged twice. -/
theorem missing_good_child_local (G : ScheduleNode → Bool) (w : ScheduleNode → ℝ) (hw : ∀ q, 0 ≤ w q)
    (start : ℕ) (κ b : ℝ) (l r : ScheduleTree)
    (hgood : G ⟨start,.split l b r,κ⟩ = true → HasInternalRoot l ∧ HasInternalRoot r) :
    missingGoodChildWeight G w ⟨start,.split l b r,κ⟩ ≤
      rootBadEdgeWeight G w start 0 (some ⟨start,.split l b r,κ⟩) l+
        rootBadEdgeWeight G w (start+l.word.length+1) κ (some ⟨start,.split l b r,κ⟩) r := by
  by_cases hg : G ⟨start,.split l b r,κ⟩ = true
  · obtain ⟨⟨ll,lr,lb,hl⟩,⟨rl,rr,rb,hr⟩⟩ := hgood hg
    subst l
    subst r
    have hWroot := hw (⟨start,.split (.split ll lb lr) b (.split rl rb rr),κ⟩ : ScheduleNode)
    by_cases hL : G ⟨start,.split ll lb lr,0⟩ = true <;>
      by_cases hR : G ⟨start+(.split ll lb lr : ScheduleTree).word.length+1,.split rl rb rr,κ⟩ = true <;>
      simp [missingGoodChildWeight,rootBadEdgeWeight,hg,hL,hR] <;> linarith only [hWroot]
  · have hL : 0 ≤ rootBadEdgeWeight G w start 0 (some ⟨start,.split l b r,κ⟩) l := by
      cases l <;> simp [rootBadEdgeWeight,hg]
    have hR : 0 ≤ rootBadEdgeWeight G w (start+l.word.length+1) κ (some ⟨start,.split l b r,κ⟩) r := by
      cases r <;> simp [rootBadEdgeWeight,hg]
    simp only [missingGoodChildWeight,hg,false_and,↓reduceIte]
    exact add_nonneg hL hR

/-- Summed missing-child weights are charged to bad-child occurrences.
The only structural requirement is that good parents have actual
internal children; the band lemmas prove this requirement. -/
theorem missing_good_child_weight_sum (G : ScheduleNode → Bool) (w : ScheduleNode → ℝ) (hw : ∀ q, 0 ≤ w q)
    (start : ℕ) (κ : ℝ) (parent : Option ScheduleNode) (t : ScheduleTree)
    (hc : AllGoodChildrenInternal G start κ t) :
    ((parentedNodes start κ parent t).map fun q => missingGoodChildWeight G w q.node).sum ≤
      ((parentedNodes start κ parent t).map (badChildEdgeWeight G w)).sum-rootBadEdgeWeight G w start κ parent t := by
  induction t generalizing start κ parent with
  | leaf hw => simp [parentedNodes,rootBadEdgeWeight]
  | split l b r il ir =>
    have hl := il start 0 (some (⟨start,.split l b r,κ⟩ : ScheduleNode)) hc.2.1
    have hr := ir (start+l.word.length+1) κ (some (⟨start,.split l b r,κ⟩ : ScheduleNode)) hc.2.2
    have hlocal := missing_good_child_local G w hw start κ b l r hc.1
    have hroot : badChildEdgeWeight G w (⟨⟨start,.split l b r,κ⟩,parent⟩ : ParentedScheduleNode) =
        rootBadEdgeWeight G w start κ parent (.split l b r) := by cases parent <;> rfl
    simp only [parentedNodes,List.map_cons,List.map_append,List.sum_cons,List.sum_append,hroot]
    linear_combination hl+hr+hlocal

end
end StrongSilver
