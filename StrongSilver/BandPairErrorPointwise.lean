-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandPairCoefficient
import StrongSilver.BandPairScoreBudget
import StrongSilver.BandExteriorDrawdown
import StrongSilver.BandEndpointGainEnvelope
import StrongSilver.BandPostPairProperties

namespace StrongSilver
open ScheduleTree BinaryForest Real Filter Set
noncomputable section
set_option maxHeartbeats 9000000

theorem levelSum_nonnegative (f : ScheduleTree → ℝ) (hf : ∀ t, 0 ≤ f t) (j : ℕ) (t : ScheduleTree) :
    0 ≤ levelSum f j t := by
  induction j generalizing t with
  | zero => cases t <;> first | exact le_rfl | exact hf _
  | succ j ih => cases t with
    | leaf word => exact le_rfl
    | split l b r => exact add_nonneg (ih l) (ih r)

theorem levelSum_abs_rootGain_capped {μ B : ℝ} (j : ℕ) (t : ScheduleTree) (hw : ∀ s ∈ t.word, s ≤ B) :
    levelSum (fun t => |rootGain (cappedStep μ B) t|) j t =
      levelSum (fun t => |rootGain (logarithmicStep μ) t|) j t := by
  induction j generalizing t with
  | zero => cases t <;> simp only [levelSum,rootGain_capped _ hw]
  | succ j ih =>
    cases t with
    | leaf word => rfl
    | split l b r =>
      exact congrArg₂ (·+·)
        (ih l (fun s hs => hw s ((left_word_sublist l r b).subset hs)))
        (ih r (fun s hs => hw s ((right_word_sublist l r b).subset hs)))

def bandPairEndpointCost (μ u : ℝ) (q : LinkedGap) : ℝ :=
  levelSum (fun t => |rootGain (logarithmicStep μ) t|) (fourPhaseDepth u) q.node.source+
  levelSum (fun t => |rootGain (logarithmicStep μ) t|) (fourPhaseDepth u+1) q.node.source

theorem bandPairEndpointCost_nonnegative (μ u : ℝ) (q : LinkedGap) : 0 ≤ bandPairEndpointCost μ u q :=
  add_nonneg (levelSum_nonnegative _ (fun _ => abs_nonneg _) _ _) (levelSum_nonnegative _ (fun _ => abs_nonneg _) _ _)

/-- The local error is bounded using the actual original gap mass,
band curvature, common scales, and exact following-pivot drawdown. -/
theorem eventually_band_pair_error_pointwise : ∀ᶠ u : ℝ in atTop,
    ∀ C κ B cap μ critical y : ℝ, ∀ h : List ℝ, ∀ q : LinkedGap,
    0 < C → BandSourceData κ B cap μ critical u h → y ∈ Icc (outerBandLow u) (outerBandHigh u) →
    q ∈ bandLinkedFrontier κ B μ u y h → BandRootCandidate B μ u (Real.log u/200) q y →
    max (silverDepthGain (cappedStep μ B) (fourPhaseDepth u) q.node.source) 0 ≤
      max (bandPairScore C B μ u y q) 0+
      6*C*bandTolerance u*bandPairEndpointCost μ u q+2*C/u+
      8*optionalNodeCharge (bandGoodDrawdownCharge B μ u) q.following := by
  filter_upwards [eventually_band_candidate_scale,eventually_band_pair_coefficient,eventually_band_pair_group_error,
    eventually_gt_atTop (0:ℝ)] with u hScale hCoefficient hGroup hu
  intro C κ B cap μ critical y h q hC S hy hq hc
  have hSc := hScale κ B μ y h q (zero_lt_one.trans S.kappa_gt_one) S.threshold_gt_one S.threshold_small
    S.scale_upper S.mu_positive S.curvature_half hy hq hc.1
  have hM := prefixMass_positive (logarithmicStep μ) q.node.source
  have hCoeff := hCoefficient B μ y (q.node.source.prefixMass (logarithmicStep μ)) S.threshold_gt_one S.scale_upper
    S.mu_positive S.curvature_half hy hSc.2.2.2.1
  have hG := hGroup B μ y (q.node.source.prefixMass (logarithmicStep μ)) S.threshold_gt_one S.scale_upper
    S.mu_positive S.curvature_half hy hM.le hSc.2.2.2.1
  have hEp := bandPairEndpointCost_nonnegative μ u q
  have hCoefScale := mul_le_mul_of_nonneg_right hCoeff (mul_nonneg hC.le hEp)
  have hGroupScale := mul_le_mul_of_nonneg_left hG hC.le
  have hExterior := mul_le_mul_of_nonneg_left (band_candidate_exterior_charge hq hc) (by norm_num : (0:ℝ) ≤ 8)
  have hOption : 0 ≤ optionalNodeCharge (bandGoodDrawdownCharge B μ u) q.following := by
    cases q.following with
    | none => exact le_rfl
    | some p => exact bandGoodDrawdownCharge_nonnegative B μ u p
  have hδ : 0 ≤ bandTolerance u := (Real.rpow_pos_of_pos hu _).le
  have hErrors : 0 ≤ 6*C*bandTolerance u*bandPairEndpointCost μ u q+2*C/u+
      8*optionalNodeCharge (bandGoodDrawdownCharge B μ u) q.following := by positivity
  apply max_le
  · have hMax := le_max_left (bandPairScore C B μ u y q) (0:ℝ)
    dsimp only [bandPairScore,twoGapScore,bandPairEndpointCost] at hCoefScale hGroupScale hMax ⊢
    linear_combination hCoefScale+hGroupScale+hExterior+hMax
  · have hMax := le_max_right (bandPairScore C B μ u y q) (0:ℝ)
    linarith only [hMax,hErrors]

/-- All endpoint errors of post-reservation pairs are dominated by
the explicit good-visible-depth envelope. -/
theorem eventually_band_selected_endpoint_cost : ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ critical y : ℝ, ∀ h : List ℝ, ∀ R : List CutPhase,
    BandSourceData κ B cap μ critical u h → y ∈ Icc (outerBandLow u) (outerBandHigh u) →
    Real.exp (nu*y)*((bandPostReservedPairs κ B μ u (Real.log u/200) (fourPhaseDepth u+1) h R y).map
      fun p => bandPairEndpointCost μ u p.1).sum ≤ bandEndpointGainEnvelope κ B μ u h y := by
  classical
  filter_upwards [eventually_band_candidate_scale] with u hScale
  intro κ B cap μ critical y h R S hy
  let G := bandGoodBool B μ u
  let F := bandGoodGainCharge B μ u
  let d := fourPhaseDepth u
  let qs := bandLinkedFrontier κ B μ u y h
  let ps := bandPostReservedPairs κ B μ u (Real.log u/200) (d+1) h R y
  let Q := fun q : LinkedGap => if GoodLinkedRoot B μ u q then Real.exp (nu*y)*
    (goodDepthSum G F d (q.node.source.indexedTree q.node.start q.node.reserve)+
      goodDepthSum G F (d+1) (q.node.source.indexedTree q.node.start q.node.reserve)) else 0
  have hQ (q : LinkedGap) : 0 ≤ Q q := by
    dsimp only [Q]
    split_ifs
    · exact mul_nonneg (Real.exp_pos _).le (add_nonneg
        (goodDepthSum_nonnegative G F (bandGoodGainCharge_nonnegative B μ u) _ _)
        (goodDepthSum_nonnegative G F (bandGoodGainCharge_nonnegative B μ u) _ _))
    · exact le_rfl
  have hSub := bandPostReservedPairs_adjacent_sublist κ B μ u (Real.log u/200) (d+1) h R y
  have hPoint : ∀ p ∈ ps, Real.exp (nu*y)*bandPairEndpointCost μ u p.1 ≤ Q p.1 := by
    intro p hp
    have hPre := bandPostReservedPairs_pre hp
    have hMember := (adjacentOccurrences_members (hSub.subset hp)).1
    have hSc := hScale κ B μ y h p.1 (zero_lt_one.trans S.kappa_gt_one) S.threshold_gt_one S.threshold_small
      S.scale_upper S.mu_positive S.curvature_half hy hMember hPre.1.1
    have hD : GoodThrough G (d+1) (p.1.node.source.indexedTree p.1.node.start p.1.node.reserve) :=
      goodThrough_prefix (k:=2) hPre.2.2
    have hD1 : GoodThrough G (d+2) (p.1.node.source.indexedTree p.1.node.start p.1.node.reserve) :=
      goodThrough_prefix (k:=1) hPre.2.2
    have hd := goodThrough_indexed_level_sum G (fun t => |rootGain (cappedStep μ B) t|) d p.1.node.start p.1.node.reserve p.1.node.source hD
    have hd1 := goodThrough_indexed_level_sum G (fun t => |rootGain (cappedStep μ B) t|) (d+1) p.1.node.start p.1.node.reserve p.1.node.source hD1
    dsimp only [Q]
    rw [if_pos hPre.1.1]
    change Real.exp (nu*y)*bandPairEndpointCost μ u p.1 ≤ Real.exp (nu*y)*
      (goodDepthSum G (fun q => if G q then |rootGain (cappedStep μ B) q.source| else 0) d _+
        goodDepthSum G (fun q => if G q then |rootGain (cappedStep μ B) q.source| else 0) (d+1) _)
    rw [hd,hd1,levelSum_abs_rootGain_capped d _ hSc.2.2.2.2,levelSum_abs_rootGain_capped (d+1) _ hSc.2.2.2.2]
    exact le_rfl
  have hSum := List.sum_le_sum hPoint
  rw [List.sum_map_mul_left] at hSum
  have hWhole := adjacent_sublist_fst_sum_le Q qs ps hSub hQ
  have hEq : (qs.map Q).sum = bandEndpointGainEnvelope κ B μ u h y := by
    unfold bandEndpointGainEnvelope linkedGoodDepthObservable
    rw [← List.sum_map_add]
    congr 1
    apply List.map_congr_left
    intro q hq
    dsimp only [Q,qs,G,F,d]
    split_ifs <;> ring
  exact hSum.trans (hWhole.trans_eq hEq)

end
end StrongSilver
