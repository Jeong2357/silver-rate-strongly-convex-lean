-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandGoodNegativeMass

namespace StrongSilver
open ScheduleTree BinaryForest Scalar.SignedIntervals Real Filter
noncomputable section
set_option maxHeartbeats 5000000

theorem gapDrawdown_suffix_le (φ : ℝ → ℝ) {small big : ScheduleTree}
    (hs : small.word.IsSuffix big.word) : small.gapDrawdown φ ≤ big.gapDrawdown φ := by
  obtain ⟨before,hEq⟩ := List.suffix_iff_exists_eq_append.mp hs
  unfold gapDrawdown transformedWord
  rw [hEq,List.map_append]
  exact suffix_drawdown_mono _ _

/-- The left drawdown condition of the actual following good vertex
implies the exact exterior drawdown premise of the two-gap extension. -/
theorem eventually_band_candidate_drawdown : ∀ᶠ u : ℝ in atTop,
    ∀ κ B μ y width : ℝ, ∀ h : List ℝ, ∀ q : LinkedGap,
    q ∈ linkedFrontier (cappedStep μ B) (bandPad u+Real.exp y) 0 κ none none (cartesian h) →
    BandRootCandidate B μ u width q y →
    ∃ p : ScheduleNode, q.following = some p ∧
      4*q.node.source.gapDrawdown (cappedStep μ B) ≤ cappedStep μ B p.pivot := by
  filter_upwards [eventually_band_forest_spacing] with u hTol
  intro κ B μ y width h q hq hCandidate
  obtain ⟨p,hp,hGood,hUpper⟩ := hCandidate.2
  obtain ⟨l,r,b,hs,hSuffix⟩ := linkedFrontier_following_suffix hq hp
  have hg := ((bandGoodBool_iff B μ u p).mp hGood).1
  have hb : PaddedBalanced (cappedStep μ B) (bandPad u) p.reserve (bandTolerance u) (.split l b r) :=
    hs ▸ paddedGood_balanced hg
  have hD := (div_le_iff₀ (sub_pos.mpr hb.1)).mp hb.2.2.2
  have hP : 0 < bandPad u := Real.exp_pos _
  have hRoot : 0 < cappedStep μ B b := hP.trans hb.1
  have hPad := mul_nonneg hTol.1 hP.le
  have hD' : l.gapDrawdown (cappedStep μ B) ≤ bandTolerance u*cappedStep μ B b := by
    nlinarith only [hD,hPad]
  have hδ4 : 4*bandTolerance u ≤ 1 := by linarith only [hTol.2.1]
  have hScale := mul_le_mul_of_nonneg_right hδ4 hRoot.le
  have hSub := gapDrawdown_suffix_le (cappedStep μ B) hSuffix
  have hFour : 4*q.node.source.gapDrawdown (cappedStep μ B) ≤ cappedStep μ B b := by
    nlinarith only [hD',hScale,hSub]
  have hPivot : p.pivot = b := by rw [ScheduleNode.pivot,hs,rootStep_split]
  exact ⟨p,hp,by simpa only [hPivot] using hFour⟩

end
end StrongSilver
