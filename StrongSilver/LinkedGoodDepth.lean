-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.LinkedIncompleteDepth
import StrongSilver.RootCandidateCounts
import StrongSilver.BandGoodScoreBudgets

namespace StrongSilver
open ScheduleTree BinaryForest Real Filter Set MeasureTheory
noncomputable section
set_option maxHeartbeats 6400000

namespace BinaryForest

theorem goodThrough_prefix {α : Type*} {G : α → Bool} {d k : ℕ} {t : BinaryTree α}
    (h : GoodThrough G (d+k) t) : GoodThrough G d t := by
  induction d generalizing t with
  | zero => trivial
  | succ d ih =>
    rw [Nat.succ_add] at h
    cases t with
    | nil => exact False.elim h
    | node v l r => exact ⟨h.1,ih h.2.1,ih h.2.2⟩

end BinaryForest

theorem goodThrough_indexed_level_sum (G : ScheduleNode → Bool) (f : ScheduleTree → ℝ)
    (j start : ℕ) (κ : ℝ) (t : ScheduleTree) (hg : GoodThrough G (j+1) (t.indexedTree start κ)) :
    goodDepthSum G (fun q => if G q then f q.source else 0) j (t.indexedTree start κ) = levelSum f j t := by
  induction j generalizing start κ t with
  | zero =>
    cases t with
    | leaf word => exact False.elim hg
    | split l b r =>
      have hG : G ⟨start,.split l b r,κ⟩ = true := hg.1
      simp only [indexedTree,goodDepthSum,goodDepthNodes,hG,↓reduceIte,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,levelSum]
  | succ j ih =>
    cases t with
    | leaf word => exact False.elim hg
    | split l b r =>
      have hG : G ⟨start,.split l b r,κ⟩ = true := hg.1
      simp only [indexedTree,goodDepthSum,goodDepthNodes,hG,↓reduceIte,List.map_append,List.sum_append,levelSum]
      exact congrArg₂ (·+·) (ih start 0 l hg.2.1) (ih (start+l.word.length+1) κ r hg.2.2)

def linkedGoodDepthObservable (κ B μ u : ℝ) (k : ℕ) (F : ScheduleNode → ℝ) (h : List ℝ) (y : ℝ) : ℝ := by
  classical
  exact ((bandLinkedFrontier κ B μ u y h).map fun q => if GoodLinkedRoot B μ u q then
    Real.exp (nu*y)*goodDepthSum (bandGoodBool B μ u) F k (q.node.source.indexedTree q.node.start q.node.reserve) else 0).sum

/-- The cutoff observable is exactly the original occurrence sum with
height visibility, including each actual depth subtree. -/
theorem linkedGoodDepthObservable_eq {κ B μ u y : ℝ} (k : ℕ) (F : ScheduleNode → ℝ) (h : List ℝ)
    (hB : 1 < B) (hμ : 0 < μ) (hμB : μ*B ≤ 1/2) :
    linkedGoodDepthObservable κ B μ u k F h y = goodVisibleDepthTotal (bandGoodBool B μ u)
      (nodePaddedHeight (cappedStep μ B) (bandPad u)) F nu k none ((cartesian h).indexedTree 0 κ) y := by
  classical
  let G := bandGoodBool B μ u
  let H := nodePaddedHeight (cappedStep μ B) (bandPad u)
  let FF := fun q : ParentedScheduleNode => if GoodHeightVisible G H q.parent q.node y then
    Real.exp (nu*y)*goodDepthSum G F k (q.node.source.indexedTree q.node.start q.node.reserve) else 0
  have hφ := cappedStep_monotone (B:=B) hμ (by linarith only [hμB])
  have hSum := linkedFrontier_sum_visible (cappedStep μ B) hφ (bandPad u+Real.exp y) 0 κ none none (cartesian h)
    (cartesian_valid h) trivial FF (by
      intro q hq hLeaf
      dsimp only [FF]
      apply if_neg
      intro hh
      exact hLeaf (bandGoodBool_internal hh.1)) (by
      intro q hq hHidden
      dsimp only [FF]
      apply if_neg
      intro hh
      have hGoodVis := (band_good_height_visible_iff B μ u y q).mp hh
      obtain ⟨p,hp,hgp,hvis⟩ := hGoodVis.2
      exact hHidden hvis)
  rw [← indexed_goodVisibleDepthTotal G H F nu y k 0 κ none (cartesian h)] at hSum
  rw [← hSum]
  unfold linkedGoodDepthObservable
  congr 1
  apply List.map_congr_left
  intro q hq
  dsimp only [FF,LinkedGap.toParented,G,H]
  simp only [← linked_good_root_height_visible hB hq]

theorem linkedGoodDepthObservable_integrable {κ B μ u a b : ℝ} (k : ℕ) (F : ScheduleNode → ℝ) (h : List ℝ)
    (hB : 1 < B) (hμ : 0 < μ) (hμB : μ*B ≤ 1/2) :
    IntervalIntegrable (linkedGoodDepthObservable κ B μ u k F h) volume a b := by
  have he : linkedGoodDepthObservable κ B μ u k F h = fun y => goodVisibleDepthTotal (bandGoodBool B μ u)
      (nodePaddedHeight (cappedStep μ B) (bandPad u)) F nu k none ((cartesian h).indexedTree 0 κ) y := by
    funext y
    exact linkedGoodDepthObservable_eq k F h hB hμ hμB
  rw [he]
  exact goodVisibleDepthTotal_integrable _ _ _ _ a b _ _ _

theorem eventually_band_linked_good_depth_transport : ∃ C > 0, ∀ᶠ u : ℝ in atTop,
    ∀ κ B μ a b : ℝ, ∀ h : List ℝ, ∀ k : ℕ, ∀ F : ScheduleNode → ℝ,
    0 ≤ κ → 1 < B → 0 < μ → μ*B ≤ 1/2 → a ≤ b → k ≤ fourPhaseDepth u+2 → (∀ q, 0 ≤ F q) →
    (∫ y in a..b, linkedGoodDepthObservable κ B μ u k F h y) ≤
      C*(2:ℝ)^k*((labels ((cartesian h).indexedTree 0 κ)).map fun q =>
        Real.exp (nu*nodePaddedHeight (cappedStep μ B) (bandPad u) q)*F q).sum := by
  classical
  obtain ⟨C,hC,H⟩ := eventually_band_actual_depth_transport
  refine ⟨C,hC,?_⟩
  filter_upwards [H] with u hBudget
  intro κ B μ a b h k F hκ hB hμ hμB hab hk hF
  have hh := hBudget κ B μ a b h k F hκ hB hμB hab hk hF
  have he : (fun y => linkedGoodDepthObservable κ B μ u k F h y) = fun y =>
      ((parentedNodes 0 κ none (cartesian h)).map fun q =>
        if @GoodHeightVisible ScheduleNode (bandGoodBool B μ u) (nodePaddedHeight (cappedStep μ B) (bandPad u)) q.parent q.node y then
          Real.exp (nu*y)*goodDepthSum (bandGoodBool B μ u) F k (q.node.source.indexedTree q.node.start q.node.reserve) else 0).sum := by
    funext y
    rw [linkedGoodDepthObservable_eq k F h hB hμ hμB,indexed_goodVisibleDepthTotal]
  rw [he]
  exact hh

end
end StrongSilver
