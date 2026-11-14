-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandGoodScoreBudgets
import StrongSilver.LinkedFollowingIntegral
import StrongSilver.BandCandidateDrawdown
import StrongSilver.BandSourceData
import StrongSilver.RootCandidateCounts

namespace StrongSilver
open ScheduleTree BinaryForest Real Filter Set MeasureTheory
noncomputable section
set_option maxHeartbeats 5300000

def bandGoodDrawdownCharge (B μ u : ℝ) : ScheduleNode → ℝ :=
  bandGoodScore B μ u (fun q => nodeLeftDrawdown (cappedStep μ B) q.source/(cappedStep μ B q.pivot-bandPad u))

theorem nodeLeftDrawdown_nonnegative (φ : ℝ → ℝ) (t : ScheduleTree) : 0 ≤ nodeLeftDrawdown φ t := by
  cases t with
  | leaf word => exact le_rfl
  | split l b r => exact gapDrawdown_nonnegative φ l

theorem bandGoodDrawdownCharge_nonnegative (B μ u : ℝ) (q : ScheduleNode) : 0 ≤ bandGoodDrawdownCharge B μ u q := by
  unfold bandGoodDrawdownCharge bandGoodScore
  split_ifs with hg
  · have hPred := ((bandGoodBool_iff B μ u q).mp hg).2
    exact div_nonneg (nodeLeftDrawdown_nonnegative _ _) (sub_pos.mpr hPred.1).le
  · exact le_rfl

/-- The exterior loss of an actual candidate gap is charged to the
left drawdown of its exact following good original pivot occurrence. -/
theorem band_candidate_exterior_charge {κ B μ u width y : ℝ} {h : List ℝ} {q : LinkedGap}
    (hq : q ∈ bandLinkedFrontier κ B μ u y h) (hc : BandRootCandidate B μ u width q y) :
    q.node.source.gapDrawdown (cappedStep μ B)/(cappedStep μ B (q.followingStep 0)) ≤
      optionalNodeCharge (bandGoodDrawdownCharge B μ u) q.following := by
  obtain ⟨p,hp,hGood,_⟩ := hc.2
  obtain ⟨l,r,b,hs,hSuffix⟩ := linkedFrontier_following_suffix hq hp
  have hPred := ((bandGoodBool_iff B μ u p).mp hGood).2
  have hDen : 0 < cappedStep μ B p.pivot-bandPad u := sub_pos.mpr hPred.1
  have hPos : 0 < cappedStep μ B p.pivot := (Real.exp_pos _).trans hPred.1
  have hSub := gapDrawdown_suffix_le (cappedStep μ B) hSuffix
  have hFollows : q.followingStep 0 = p.pivot := by simp only [LinkedGap.followingStep,hp,Option.map_some,Option.getD_some]
  have hLeft : nodeLeftDrawdown (cappedStep μ B) p.source = l.gapDrawdown (cappedStep μ B) := by rw [hs]; rfl
  rw [hFollows,hp]
  simp only [optionalNodeCharge,bandGoodDrawdownCharge,bandGoodScore,hGood,↓reduceIte]
  calc
    _ ≤ q.node.source.gapDrawdown (cappedStep μ B)/(cappedStep μ B p.pivot-bandPad u) :=
      div_le_div_of_nonneg_left (gapDrawdown_nonnegative _ _) hDen (by have hh := Real.exp_pos ((987:ℝ)/1000*u); change 0 < bandPad u at hh; linarith only [hh])
    _ ≤ _ := by rw [hLeft]; exact div_le_div_of_nonneg_right hSub hDen.le

/-- The measurable source envelope for all exterior pair losses has
an O(W) integral, uniformly before a reservation is chosen. -/
theorem eventually_band_exterior_envelope_budget : ∃ C > 0, ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ critical a b : ℝ, ∀ h : List ℝ,
    BandSourceData κ B cap μ critical u h → a ≤ b →
    (∫ y in a..b, linkedFollowingObservable (cappedStep μ B) (bandPad u) κ nu (bandGoodDrawdownCharge B μ u) h y) ≤
      C*weightedCount h cap := by
  obtain ⟨C,hC,H⟩ := eventually_band_good_drawdown_budget
  refine ⟨C/nu,div_pos hC nu_positive,?_⟩
  filter_upwards [H] with u hBudget
  intro κ B cap μ critical a b h S hab
  have hφ := cappedStep_monotone (B:=B) S.mu_positive (by linarith only [S.curvature_half])
  have hIntegral := linkedFollowingObservable_integral_upper (cappedStep μ B) hφ (bandPad u) κ nu a b
    (bandGoodDrawdownCharge B μ u) h nu_positive.le (bandGoodDrawdownCharge_nonnegative B μ u) hab
  have hBound := hBudget κ B cap μ critical h S.kappa_gt_one S.threshold_gt_one S.threshold_le_cap S.cap_le_kappa S.scale_upper
    S.curvature_lower S.curvature_upper S.curvature_half S.noncritical S.critical_charge S.critical_rank S.distance_stable S.threshold_count S.rank_lower
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ nu_positive).mpr
  dsimp only [bandGoodDrawdownCharge] at hIntegral ⊢
  linear_combination hIntegral+hBound

end
end StrongSilver
