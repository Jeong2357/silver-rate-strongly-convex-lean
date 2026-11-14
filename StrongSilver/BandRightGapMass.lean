-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.LinkedFollowingSplit
import StrongSilver.LinkedFollowingMembership
import StrongSilver.GoodThroughSourceBalance
import StrongSilver.CartesianFollowingSplit
import StrongSilver.CutMasses
import StrongSilver.BandRootCandidates

namespace StrongSilver
open ScheduleTree BinaryForest Real Filter
noncomputable section
set_option maxHeartbeats 6200000

theorem eventually_band_scaled_tolerance_small {ε : ℝ} (hε : 0 < ε) : ∀ᶠ u : ℝ in atTop, 4*bandTolerance u ≤ ε := by
  have ht := tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/10)
  filter_upwards [ht.eventually (gt_mem_nhds (show (0:ℝ) < ε/4 by positivity))] with u hu
  have hh : bandTolerance u ≤ ε/4 := by simpa only [bandTolerance,neg_div] using hu.le
  linarith only [hh]

/-- The actual right gap has the sharp mass bound needed for the
ordinary suffix construction, using its exact following split. -/
theorem eventually_band_right_gap_mass : ∀ᶠ u : ℝ in atTop,
    ∀ κ B μ y width : ℝ, ∀ h : List ℝ, ∀ q r : LinkedGap,
    0 < κ → 1 < B → B ≤ κ/128 → u ≤ firstAverageLogScale B → 0 < μ → μ*B ≤ 1/2 →
    (q,r) ∈ adjacentOccurrences (linkedFrontier (cappedStep μ B) (bandPad u+Real.exp y) 0 κ none none (cartesian h)) →
    BandRootCandidate B μ u width q y →
    ∃ p : ScheduleNode, q.following = some p ∧
      transformedGapMaximum μ r.node.source.word+1 ≤ (14/5:ℝ)*cappedStep μ B p.pivot := by
  filter_upwards [eventually_band_good_source_balance,eventually_eligible_band_step_upper,
    eventually_band_scaled_tolerance_small (by norm_num : (0:ℝ) < 1/100)] with u hBalance hEligible hTolerance
  intro κ B μ y width h q r hκ hB hBκ hU hμ hμB hPair hCandidate
  have hMembers := adjacentOccurrences_members hPair
  obtain ⟨p,hp,hGood,hUpper⟩ := hCandidate.2
  have hMem := linkedFrontier_following_mem hMembers.1 hp
  have hSilver := hBalance κ B μ h p hκ hB hBκ hU hμ hμB hMem hGood
  obtain ⟨p',l,r',b,hp',hs,hSuffix,hPrefix⟩ := linkedFrontier_following_split hPair
  have hEq : p' = p := Option.some.inj (hp'.symm.trans hp)
  subst p'
  have hSilver' : SilverBalanced (cappedStep μ B) (4*bandTolerance u) (.split l b r') := hs ▸ hSilver
  have hMass := right_gap_mass_bound hPrefix hTolerance hSilver'
  have hCart := indexedTree_source_cartesian (cartesian_valid h) hMem
  rw [hs] at hCart
  have hPred := ((bandGoodBool_iff B μ u p).mp hGood).2
  have hpB := hEligible B μ p.pivot p.pivotIndex hB hU hμ hμB (bandProtectedPredicate_eligible hPred)
  have hPivot : p.pivot = b := by rw [ScheduleNode.pivot,hs,rootStep_split]
  rw [hPivot] at hpB
  have hWord : ∀ a ∈ r.node.source.word, a ≤ B := fun a ha =>
    (hCart.2.2.2.2 a (hPrefix.sublist.subset ha)).trans hpB
  have hTransform := capped_gapPrefix_eq hμ (show μ*B < 1 by linarith only [hμB]) r.node.source.word hWord
  change gapPrefix (cappedStep μ B) r.node.source.word+1 ≤ (14/5:ℝ)*cappedStep μ B b at hMass
  rw [hTransform] at hMass
  exact ⟨p,hp,by simpa only [hPivot] using hMass⟩

end
end StrongSilver
