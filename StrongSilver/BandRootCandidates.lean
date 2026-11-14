-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandLinkedNonterminal
import StrongSilver.BandBadRootParent
import StrongSilver.LargeFollowingIntegral
import StrongSilver.LinkedDynamicObservable

namespace StrongSilver
open ScheduleTree BinaryForest Real Filter Set MeasureTheory
noncomputable section
set_option maxHeartbeats 6800000

def BandRootCandidate (B μ u width : ℝ) (q : LinkedGap) (y : ℝ) : Prop :=
  GoodLinkedRoot B μ u q ∧ ∃ p, q.following = some p ∧ bandGoodBool B μ u p = true ∧
    cappedStep μ B p.pivot ≤ bandPad u+Real.exp (y+width)

def rootCandidateBadIndicator (B μ u width : ℝ) (q : LinkedGap) (y : ℝ) : ℝ := by
  classical
  exact if BandRootCandidate B μ u width q y then 0 else 1

def rootCandidateExclusionObservable (κ B μ u width : ℝ) (h : List ℝ) (y : ℝ) : ℝ :=
  Real.exp (nu*y)*linkedDynamicObservable (rootCandidateBadIndicator B μ u width) (cappedStep μ B) (bandPad u) 0 κ none none (cartesian h) y

/-- Failure of the S(y) root conditions is covered by a bad root or
parent, a bad protected following pivot, or a large following pivot. -/
theorem eventually_band_candidate_exclusions_pointwise : ∀ᶠ u : ℝ in atTop,
    ∀ κ B μ y width : ℝ, ∀ h : List ℝ,
    0 < κ → 1 < B → B ≤ κ/128 → u ≤ firstAverageLogScale B → 0 < μ → μ*B ≤ 1/2 →
    outerBandLow u < y → y+width+3*visibilitySpacing ≤ outerBandHigh u →
    rootCandidateExclusionObservable κ B μ u width h y ≤
      badRootParentObservable κ B μ u h y+
        linkedFollowingObservable (cappedStep μ B) (bandPad u) κ nu (bandBadIndicator B μ u) h y+
        largeFollowingObservable (cappedStep μ B) (bandPad u) κ nu width h y := by
  classical
  filter_upwards [eventually_band_good_linked_nonterminal] with u hNonterminal
  intro κ B μ y width h hκ hB hBκ hU hμ hμB hlo hhi
  let φ := cappedStep μ B
  let P := bandPad u
  let xs := linkedFrontier φ (P+Real.exp y) 0 κ none none (cartesian h)
  let large := fun p : ScheduleNode => if P+Real.exp (y+width) < φ p.pivot then (1:ℝ) else 0
  have hLargeNonneg (p : ScheduleNode) : 0 ≤ large p := by dsimp only [large]; split_ifs <;> norm_num
  have hPoint (q : LinkedGap) (hq : q ∈ xs) : rootCandidateBadIndicator B μ u width q y ≤
      badRootParentIndicator B μ u q+optionalNodeCharge (bandBadIndicator B μ u) q.following+optionalNodeCharge large q.following := by
    have hBadNonneg := optionalNodeCharge_nonnegative (bandBadIndicator B μ u) (bandBadIndicator_nonnegative B μ u) q.following
    have hLarge := optionalNodeCharge_nonnegative large hLargeNonneg q.following
    have hRootNonneg : 0 ≤ badRootParentIndicator B μ u q := by unfold badRootParentIndicator; split_ifs <;> norm_num
    by_cases hC : BandRootCandidate B μ u width q y
    · simp only [rootCandidateBadIndicator,if_pos hC]
      exact add_nonneg (add_nonneg hRootNonneg hBadNonneg) hLarge
    · simp only [rootCandidateBadIndicator,if_neg hC]
      by_cases hRoot : GoodLinkedRoot B μ u q
      · obtain ⟨p,hp⟩ := hNonterminal κ B μ y h q hκ hB hBκ hU hμ hμB hq hRoot.1
        by_cases hL : P+Real.exp (y+width) < φ p.pivot
        · have hlargeEq : optionalNodeCharge large q.following = 1 := by simp only [optionalNodeCharge,hp,large,if_pos hL]
          rw [hlargeEq]
          linarith only [hRootNonneg,hBadNonneg]
        · have hSelected := linkedFrontier_following_selected
            (show ∀ p : ScheduleNode, (none : Option ScheduleNode) = some p → P+Real.exp y < φ p.pivot by intro p hh; cases hh) hq hp
          have hPositive : P < φ p.pivot := lt_trans (lt_add_of_pos_right _ (Real.exp_pos _)) hSelected
          have hHeightLo : y < nodePaddedHeight φ P p := by
            apply (Real.lt_log_iff_exp_lt (sub_pos.mpr hPositive)).mpr
            linarith only [hSelected]
          have hHeightHi : nodePaddedHeight φ P p ≤ y+width := by
            apply (Real.log_le_iff_le_exp (sub_pos.mpr hPositive)).mpr
            linarith only [le_of_not_gt hL]
          have hPred : bandProtectedPredicate B μ u p := by
            refine ⟨hPositive,hlo.trans hHeightLo,?_⟩
            change nodePaddedHeight φ P p+3*visibilitySpacing ≤ outerBandHigh u
            linarith only [hHeightHi,hhi]
          have hNotGood : ¬ PaddedGood φ P p.reserve (bandTolerance u) p.source := by
            intro hgood
            have hBool := (bandGoodBool_iff B μ u p).mpr ⟨hgood,hPred⟩
            exact hC ⟨hRoot,p,hp,hBool,le_of_not_gt hL⟩
          have hBadEq : optionalNodeCharge (bandBadIndicator B μ u) q.following = 1 := by
            simp only [optionalNodeCharge,hp,bandBadIndicator]
            exact if_pos ⟨hPred,hNotGood⟩
          rw [hBadEq]
          linarith only [hRootNonneg,hLarge]
      · have hRootEq : badRootParentIndicator B μ u q = 1 := if_neg hRoot
        rw [hRootEq]
        linarith only [hBadNonneg,hLarge]
  have hSum := List.sum_le_sum hPoint
  simp only [List.sum_map_add] at hSum
  have hScale := mul_le_mul_of_nonneg_left hSum (Real.exp_pos (nu*y)).le
  unfold rootCandidateExclusionObservable badRootParentObservable largeFollowingObservable linkedFollowingObservable
  rw [List.sum_map_mul_left,List.sum_map_mul_left]
  dsimp only [linkedDynamicObservable,linkedObservable,xs,large,φ,P] at hScale ⊢
  linear_combination hScale

end
end StrongSilver
