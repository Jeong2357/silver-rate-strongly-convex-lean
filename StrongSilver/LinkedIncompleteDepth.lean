-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.LinkedVisibleSums
import StrongSilver.BandIncompleteDepth
import StrongSilver.BandRootCandidates

namespace StrongSilver
open ScheduleTree BinaryForest Real Set MeasureTheory
noncomputable section
set_option maxHeartbeats 6400000

local instance linkedIncompleteHeightDecidable (G : ScheduleNode → Bool) (H : ScheduleNode → ℝ)
    (parent : Option ScheduleNode) (q : ScheduleNode) (y : ℝ) : Decidable (GoodHeightVisible G H parent q y) := Classical.propDecidable _
local instance linkedIncompleteThroughDecidable (G : ScheduleNode → Bool) (n : ℕ) (t : BinaryTree ScheduleNode) : Decidable (GoodThrough G n t) := Classical.propDecidable _

theorem indexed_incompleteVisibleTotal (G : ScheduleNode → Bool) (H : ScheduleNode → ℝ)
    (v y : ℝ) (n start : ℕ) (κ : ℝ) (parent : Option ScheduleNode) (t : ScheduleTree) :
    incompleteVisibleTotal G H v n parent (t.indexedTree start κ) y =
      ((parentedNodes start κ parent t).map fun q =>
        if GoodHeightVisible G H q.parent q.node y ∧ ¬ GoodThrough G (n+2) (q.node.source.indexedTree q.node.start q.node.reserve)
          then Real.exp (v*y) else 0).sum := by
  classical
  induction t generalizing start κ parent with
  | leaf word => simp [indexedTree,incompleteVisibleTotal,parentedNodes]
  | split l b r il ir =>
    simp only [indexedTree,incompleteVisibleTotal,parentedNodes,List.map_cons,List.map_append,List.sum_cons,List.sum_append,il,ir]
    ring

/-- Good root/parent labels on an actual linked frontier are precisely
height-visible good occurrences. -/
theorem linked_good_root_height_visible {κ B μ u y : ℝ} {h : List ℝ} {q : LinkedGap} (hB : 1 < B)
    (hq : q ∈ linkedFrontier (cappedStep μ B) (bandPad u+Real.exp y) 0 κ none none (cartesian h)) :
    GoodLinkedRoot B μ u q ↔ GoodHeightVisible (bandGoodBool B μ u)
      (nodePaddedHeight (cappedStep μ B) (bandPad u)) q.parent q.node y := by
  have hVis := band_good_height_visible_iff B μ u y q.toParented
  dsimp only [LinkedGap.toParented] at hVis
  rw [hVis]
  constructor
  · intro hg
    obtain ⟨p,hp,hgp⟩ := hg.2
    refine ⟨hg.1,p,hp,hgp,?_⟩
    have hzero : cappedStep μ B 0 ≤ bandPad u+Real.exp y := by
      rw [cappedStep,if_pos (zero_lt_one.trans hB).le,logarithmicStep_zero]
      exact add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
    have hmem : q.node ∈ indexedFrontier (cappedStep μ B) (bandPad u+Real.exp y) 0 κ (cartesian h) := by
      rw [← linkedFrontier_erase (cappedStep μ B) (bandPad u+Real.exp y) 0 κ none none (cartesian h)]
      exact List.mem_map.mpr ⟨q,hq,rfl⟩
    have hUpper := indexedFrontier_root_upper hzero hmem
    have hParent := linkedFrontier_parent_above (show ParentedScheduleNode.parentAbove (cappedStep μ B) (bandPad u+Real.exp y) none from trivial) hq
    exact ⟨hUpper,hParent⟩
  · intro hh
    exact ⟨hh.1,by obtain ⟨p,hp,hgp,_⟩ := hh.2; exact ⟨p,hp,hgp⟩⟩

def linkedIncompleteObservable (κ B μ u : ℝ) (n : ℕ) (h : List ℝ) (y : ℝ) : ℝ := by
  classical
  exact ((linkedFrontier (cappedStep μ B) (bandPad u+Real.exp y) 0 κ none none (cartesian h)).map fun q =>
    if GoodLinkedRoot B μ u q ∧ ¬ GoodThrough (bandGoodBool B μ u) (n+2)
      (q.node.source.indexedTree q.node.start q.node.reserve) then Real.exp (nu*y) else 0).sum

/-- The actual linked-gap incomplete-subtree count is exactly the
original occurrence integral already bounded in BandIncompleteDepth. -/
theorem linkedIncompleteObservable_eq {κ B μ u y : ℝ} (n : ℕ) (h : List ℝ)
    (hB : 1 < B) (hμ : 0 < μ) (hμB : μ*B ≤ 1/2) :
    linkedIncompleteObservable κ B μ u n h y = incompleteVisibleTotal (bandGoodBool B μ u)
      (nodePaddedHeight (cappedStep μ B) (bandPad u)) nu n none ((cartesian h).indexedTree 0 κ) y := by
  classical
  let G := bandGoodBool B μ u
  let H := nodePaddedHeight (cappedStep μ B) (bandPad u)
  let F := fun q : ParentedScheduleNode => if GoodHeightVisible G H q.parent q.node y ∧
    ¬ GoodThrough G (n+2) (q.node.source.indexedTree q.node.start q.node.reserve) then Real.exp (nu*y) else 0
  have hφ := cappedStep_monotone (B:=B) hμ (by linarith only [hμB])
  have hSum := linkedFrontier_sum_visible (cappedStep μ B) hφ (bandPad u+Real.exp y) 0 κ none none (cartesian h)
    (cartesian_valid h) trivial F (by
      intro q hq hLeaf
      dsimp only [F]
      apply if_neg
      intro hh
      exact hLeaf (bandGoodBool_internal hh.1.1)) (by
      intro q hq hHidden
      dsimp only [F]
      apply if_neg
      intro hh
      have hGoodVis := (band_good_height_visible_iff B μ u y q).mp hh.1
      obtain ⟨p,hp,hgp,hvis⟩ := hGoodVis.2
      exact hHidden hvis)
  rw [← indexed_incompleteVisibleTotal G H nu y n 0 κ none (cartesian h)] at hSum
  rw [← hSum]
  unfold linkedIncompleteObservable
  congr 1
  apply List.map_congr_left
  intro q hq
  dsimp only [F,LinkedGap.toParented,G,H]
  simp only [← linked_good_root_height_visible hB hq]

end
end StrongSilver
