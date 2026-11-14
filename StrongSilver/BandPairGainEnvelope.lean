-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandPairErrorPointwise
import StrongSilver.BandPositiveLogIntegral

namespace StrongSilver
open ScheduleTree BinaryForest Real Filter Set MeasureTheory
noncomputable section
set_option maxHeartbeats 9000000

/-- A source-schedule envelope for the total positive available gain.
It contains no choice of a reservation as a function of cutoff. -/
def bandPairGainEnvelope (C κ B cap μ u : ℝ) (h : List ℝ) (y : ℝ) : ℝ :=
  4*max (Real.exp (nu*y)*bandPositiveLog κ B μ u y h) 0+
    (19216+8*C)*weightedCount h cap/u+
    6*C*bandTolerance u*bandEndpointGainEnvelope κ B μ u h y+
    8*linkedFollowingObservable (cappedStep μ B) (bandPad u) κ nu (bandGoodDrawdownCharge B μ u) h y

/-- All actual available gains are bounded pointwise by an explicit
measurable envelope before any integration over cutoffs. -/
theorem eventually_band_pair_gain_envelope : ∃ C > 0, ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ critical y : ℝ, ∀ h : List ℝ,
    BandSourceData κ B cap μ critical u h → y ∈ Icc (outerBandLow u) (outerBandHigh u) →
    ∀ s : BandPairReservation κ B cap μ u y h,
    Real.exp (nu*y)*((bandPostReservedPairs κ B μ u (Real.log u/200) (fourPhaseDepth u+1) h s.assembly.reserved y).map
      fun p => max (silverDepthGain (cappedStep μ B) (fourPhaseDepth u) p.1.node.source) 0).sum ≤
      bandPairGainEnvelope C κ B cap μ u h y := by
  classical
  obtain ⟨C,hC,H⟩ := eventually_band_pair_score_budget
  refine ⟨C,hC,?_⟩
  filter_upwards [H,eventually_band_pair_error_pointwise,eventually_band_selected_endpoint_cost,
    eventually_band_top_frontier,eventually_gt_atTop (0:ℝ)] with u hScore hError hEndpoint hTop hu
  intro κ B cap μ critical y h S hy s
  let ps := bandPostReservedPairs κ B μ u (Real.log u/200) (fourPhaseDepth u+1) h s.assembly.reserved y
  let qs := bandLinkedFrontier κ B μ u y h
  let F := fun q : LinkedGap => optionalNodeCharge (bandGoodDrawdownCharge B μ u) q.following
  have hF (q : LinkedGap) : 0 ≤ F q := by
    dsimp only [F]
    cases q.following with
    | none => exact le_rfl
    | some p => exact bandGoodDrawdownCharge_nonnegative B μ u p
  have hSub := bandPostReservedPairs_adjacent_sublist κ B μ u (Real.log u/200) (fourPhaseDepth u+1) h s.assembly.reserved y
  have hPoint : ∀ p ∈ ps,
      max (silverDepthGain (cappedStep μ B) (fourPhaseDepth u) p.1.node.source) 0 ≤
      max (bandPairScore C B μ u y p.1) 0+6*C*bandTolerance u*bandPairEndpointCost μ u p.1+2*C/u+8*F p.1 := by
    intro p hp
    have hPre := bandPostReservedPairs_pre hp
    exact hError C κ B cap μ critical y h p.1 hC S hy (adjacentOccurrences_members (hSub.subset hp)).1 hPre.1
  have hSum := List.sum_le_sum hPoint
  simp only [List.sum_map_add,List.sum_map_mul_left,List.map_const',List.sum_replicate,nsmul_eq_mul] at hSum
  have hWeighted := mul_le_mul_of_nonneg_left hSum (Real.exp_pos (nu*y)).le
  have hScoreBound := hScore κ B cap μ critical h S.kappa_gt_one S.threshold_gt_one S.threshold_le_cap S.cap_le_kappa S.threshold_small
    S.scale_upper S.curvature_lower S.curvature_upper S.curvature_threshold S.noncritical S.critical_charge S.critical_rank S.distance_stable y hy s
  have hEndpointBound := hEndpoint κ B cap μ critical y h s.assembly.reserved S hy
  have hδ : 0 ≤ bandTolerance u := (Real.rpow_pos_of_pos hu _).le
  have hEndpointScale := mul_le_mul_of_nonneg_left hEndpointBound (show 0 ≤ 6*C*bandTolerance u by positivity)
  have hExterior := adjacent_sublist_fst_sum_le F qs ps hSub hF
  have hExteriorScale := mul_le_mul_of_nonneg_left hExterior (show 0 ≤ 8*Real.exp (nu*y) by positivity)
  have hCountNat : ps.length ≤ qs.length := hSub.length_le.trans
    (by simpa only [List.length_map] using (adjacentOccurrences_fst_sublist qs).length_le)
  have hCount : (ps.length:ℝ) ≤ (qs.length:ℝ) := by exact_mod_cast hCountNat
  have hCountWeight := mul_le_mul_of_nonneg_left hCount (Real.exp_pos (nu*y)).le
  have hTopBound := hTop κ B cap μ y h S.threshold_gt_one S.threshold_le_cap S.scale_upper S.mu_positive S.curvature_half hy S.threshold_count
  rw [← bandLinkedFrontier_length] at hTopBound
  have hCountBound : Real.exp (nu*y)*(ps.length:ℝ) ≤ 4*weightedCount h cap := hCountWeight.trans hTopBound
  have hCountScale := mul_le_mul_of_nonneg_left hCountBound (show 0 ≤ 2*C/u by positivity)
  have hExteriorEq : Real.exp (nu*y)*(qs.map F).sum =
      linkedFollowingObservable (cappedStep μ B) (bandPad u) κ nu (bandGoodDrawdownCharge B μ u) h y := by
    unfold linkedFollowingObservable
    rw [List.sum_map_mul_left]
    rfl
  dsimp only [ps,qs] at hWeighted hCountScale hExteriorScale
  unfold bandPairGainEnvelope
  rw [show (8*Real.exp (nu*y))*((qs.map F).sum) = 8*(Real.exp (nu*y)*(qs.map F).sum) by ring,
    hExteriorEq] at hExteriorScale
  linear_combination hWeighted+hScoreBound+hEndpointScale+hCountScale+hExteriorScale

theorem bandPairGainEnvelope_integrable {κ B cap μ u a b C : ℝ} (h : List ℝ)
    (hB : 1 < B) (hμ : 0 < μ) (hμB : μ*B ≤ 1/2) :
    IntervalIntegrable (bandPairGainEnvelope C κ B cap μ u h) volume a b :=
  ((((intervalIntegrable_positive_part (bandPositiveLog_weighted_integrable κ B μ u a b h)).const_mul 4).add
    intervalIntegrable_const).add ((bandEndpointGainEnvelope_integrable h hB hμ hμB).const_mul (6*C*bandTolerance u))).add
      ((linkedFollowingObservable_integrable (cappedStep μ B) (cappedStep_monotone hμ (by linarith only [hμB]))
        (bandPad u) κ nu a b (bandGoodDrawdownCharge B μ u) h).const_mul 8)

end
end StrongSilver
