-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.GoodNodeNegativeMass
import StrongSilver.BandGoodChildGeometry
import StrongSilver.LinkedFollowingSuffix
import StrongSilver.BandRootCandidates

namespace StrongSilver
open ScheduleTree BinaryForest Scalar.SignedIntervals Real Filter
noncomputable section
set_option maxHeartbeats 5800000

theorem negativeMass_sublist_le {small big : List ℝ} (hsub : small.Sublist big) : negativeMass small ≤ negativeMass big := by
  apply (hsub.map (fun x => max (-x) 0)).sum_le_sum
  intro x hx
  obtain ⟨b,_,rfl⟩ := List.mem_map.mp hx
  exact le_max_right _ _

/-- Good original indexed labels provide the actual signed negative
mass of their left child, as required by the trajectory construction. -/
theorem eventually_band_good_original_negative_mass : ∀ᶠ u : ℝ in atTop,
    ∀ κ B μ : ℝ, ∀ h : List ℝ, ∀ q : ScheduleNode, ∀ l r : ScheduleTree, ∀ b : ℝ,
    0 ≤ κ → 1 < B → u ≤ firstAverageLogScale B → 0 < μ → μ*B ≤ 1/2 →
    q ∈ labels ((cartesian h).indexedTree 0 κ) → bandGoodBool B μ u q = true → q.source = .split l b r →
    negativeMass l.word ≤ 2*bandTolerance u*cappedStep μ B b := by
  filter_upwards [eventually_good_node_negative_mass,eventually_band_forest_spacing] with u H hTol
  intro κ B μ h q l r b hκ hB hU hμ hμB hq hg hs
  have hParented : q ∈ (parentedNodes 0 κ none (cartesian h)).map ParentedScheduleNode.node := by rwa [parentedNodes_erase]
  obtain ⟨p,hp,hpq⟩ := List.mem_map.mp hParented
  have hG := (bandGoodBool_iff B μ u q).mp hg
  have hPred : bandProtectedPredicate B μ u p.node := hpq ▸ hG.2
  have hGood : PaddedGood (cappedStep μ B) (bandPad u) p.node.reserve (bandTolerance u) p.node.source := hpq ▸ hG.1
  have hSource : p.node.source = .split l b r := by simpa only [hpq] using hs
  exact H κ B μ (bandTolerance u) h p l r b hκ hB hU hμ hμB hTol.1 (hTol.2.1.trans (by norm_num))
    (bandProtectedNodes_mem_of_predicate hp hPred) hSource hGood

/-- Every actual candidate gap inherits its following good pivot's
original signed left-mass budget. The relation is the exact original
word suffix, rather than a comparison of equal pivot values. -/
theorem eventually_band_candidate_gap_negative_mass : ∀ᶠ u : ℝ in atTop,
    ∀ κ B μ y width : ℝ, ∀ h : List ℝ, ∀ q : LinkedGap,
    0 ≤ κ → 1 < B → u ≤ firstAverageLogScale B → 0 < μ → μ*B ≤ 1/2 →
    q ∈ linkedFrontier (cappedStep μ B) (bandPad u+Real.exp y) 0 κ none none (cartesian h) →
    BandRootCandidate B μ u width q y →
    ∃ p : ScheduleNode, q.following = some p ∧
      negativeMass q.node.source.word ≤ 2*bandTolerance u*cappedStep μ B p.pivot ∧
      cappedStep μ B p.pivot ≤ bandPad u+Real.exp (y+width) := by
  filter_upwards [eventually_band_good_original_negative_mass] with u H
  intro κ B μ y width h q hκ hB hU hμ hμB hq hCandidate
  obtain ⟨p,hp,hGood,hUpper⟩ := hCandidate.2
  have hMem := linkedFrontier_following_mem hq hp
  obtain ⟨l,r,b,hs,hSuffix⟩ := linkedFrontier_following_suffix hq hp
  have hLeft := H κ B μ h p l r b hκ hB hU hμ hμB hMem hGood hs
  have hNeg := (negativeMass_sublist_le hSuffix.sublist).trans hLeft
  have hPivot : p.pivot = b := by rw [ScheduleNode.pivot,hs,rootStep_split]
  refine ⟨p,hp,?_,hUpper⟩
  simpa only [hPivot] using hNeg

end
end StrongSilver
