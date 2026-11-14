-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.GoodThroughFailure
import StrongSilver.CartesianBalancedScales
import StrongSilver.CartesianFourGapGroups
import StrongSilver.BandSilverBalance
import StrongSilver.BandGoodChildGeometry

namespace StrongSilver
open ScheduleTree BinaryForest Real Filter
noncomputable section
set_option maxHeartbeats 5800000

/-- Complete good indexed subtrees give completeness and balance on
the actual original signed Cartesian source intervals. -/
theorem goodThrough_indexed_source_balance (G : ScheduleNode → Bool) (φ : ℝ → ℝ) (ε : ℝ)
    (n start : ℕ) (κ : ℝ) (t : ScheduleTree)
    (hG : ∀ q ∈ labels (t.indexedTree start κ), G q = true → SilverBalanced φ ε q.source)
    (hg : GoodThrough G n (t.indexedTree start κ)) :
    completeThrough n t ∧ balancedThrough φ ε n t := by
  induction n generalizing start κ t with
  | zero => exact ⟨trivial,trivial⟩
  | succ n ih =>
    cases t with
    | leaf word => exact False.elim hg
    | split l b r =>
      have hroot : SilverBalanced φ ε (.split l b r) :=
        hG ⟨start,.split l b r,κ⟩ (by simp [indexedTree,labels]) hg.1
      have hL := ih start 0 l (by
        intro q hq
        apply hG q
        simp only [indexedTree,labels,List.mem_cons,List.mem_append]
        exact Or.inr (Or.inl hq)) hg.2.1
      have hR := ih (start+l.word.length+1) κ r (by
        intro q hq
        apply hG q
        simp only [indexedTree,labels,List.mem_cons,List.mem_append]
        exact Or.inr (Or.inr hq)) hg.2.2
      exact ⟨⟨hL.1,hR.1⟩,hroot,hL.2,hR.2⟩

/-- Every good original occurrence supplies the exact offset-one
SilverBalanced premise used by the finite depth trajectory. -/
theorem eventually_band_good_source_balance : ∀ᶠ u : ℝ in atTop,
    ∀ κ B μ : ℝ, ∀ h : List ℝ, ∀ q : ScheduleNode,
    0 < κ → 1 < B → B ≤ κ/128 → u ≤ firstAverageLogScale B → 0 < μ → μ*B ≤ 1/2 →
    q ∈ labels ((cartesian h).indexedTree 0 κ) → bandGoodBool B μ u q = true →
    SilverBalanced (cappedStep μ B) (4*bandTolerance u) q.source := by
  filter_upwards [eventually_band_silver_balance,eventually_band_forest_spacing] with u hSilver hTol
  intro κ B μ h q hκ hB hBκ hU hμ hμB hq hGood
  have hParented : q ∈ (parentedNodes 0 κ none (cartesian h)).map ParentedScheduleNode.node := by rwa [parentedNodes_erase]
  obtain ⟨p,hp,hpq⟩ := List.mem_map.mp hParented
  have hG := (bandGoodBool_iff B μ u q).mp hGood
  have hpred : bandProtectedPredicate B μ u p.node := hpq ▸ hG.2
  have hbal : PaddedBalanced (cappedStep μ B) (bandPad u) p.node.reserve (bandTolerance u) p.node.source :=
    hpq ▸ paddedGood_balanced hG.1
  have hProtected := bandProtectedNodes_mem_of_predicate hp hpred
  have hδmax : bandTolerance u ≤ 1/4 := hTol.2.1.trans (by norm_num)
  have H := hSilver κ B μ h p hκ hB hBκ hU hμ hμB hδmax hProtected hbal
  simpa only [hpq] using H

end
end StrongSilver
