-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandSourceData
import StrongSilver.BandGapDepthComparison
import StrongSilver.IndexedDepthPrefixSum

namespace StrongSilver
open ScheduleTree BinaryForest Real Filter
noncomputable section
set_option maxHeartbeats 6200000

/-- The offset-one power inequality on every actual original good
occurrence, divided by that occurrence's exact exponential weight. -/
theorem eventually_band_good_unit_power : ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ critical : ℝ, ∀ h : List ℝ, ∀ q : ScheduleNode,
    BandSourceData κ B cap μ critical u h → q ∈ labels ((cartesian h).indexedTree 0 κ) → bandGoodBool B μ u q = true →
    normalizedNodeDecrease (cappedStep μ B) (bandPad u) q ≤
      splitCoefficient*rootGain (cappedStep μ B) q.source+
      splitCoefficient*bandTolerance u*|rootGain (cappedStep μ B) q.source|+16*splitCoefficient*Real.exp (-u/100) := by
  filter_upwards [eventually_band_unit_pointwise,eventually_band_forest_spacing] with u hUnit hTol
  intro κ B cap μ critical h q S hq hg
  have hParented : q ∈ (parentedNodes 0 κ none (cartesian h)).map ParentedScheduleNode.node := by rwa [parentedNodes_erase]
  obtain ⟨p,hp,hpq⟩ := List.mem_map.mp hParented
  have hGood := (bandGoodBool_iff B μ u q).mp hg
  have hPred : bandProtectedPredicate B μ u p.node := hpq ▸ hGood.2
  have hProtected := bandProtectedNodes_mem_of_predicate hp hPred
  have hBalanced : PaddedBalanced (cappedStep μ B) (bandPad u) p.node.reserve (bandTolerance u) p.node.source :=
    hpq ▸ paddedGood_balanced hGood.1
  have hBound := (hUnit κ B μ (bandTolerance u) h p (zero_lt_one.trans S.kappa_gt_one) S.threshold_gt_one S.threshold_small
    S.scale_upper S.mu_positive S.curvature_half hTol.1 (hTol.2.1.trans (by norm_num)) hProtected hBalanced).1
  simp only [parentedHeight,hpq] at hBound
  unfold normalizedNodeDecrease
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  dsimp only [nodePaddedHeight]
  linear_combination hBound

/-- Summing over any complete actual good depth prefix preserves the
original signed S_d contributions and their explicit local errors. -/
theorem eventually_band_good_prefix_power : ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ critical : ℝ, ∀ h : List ℝ, ∀ q : ScheduleNode, ∀ k : ℕ,
    BandSourceData κ B cap μ critical u h → q ∈ labels ((cartesian h).indexedTree 0 κ) →
    GoodThrough (bandGoodBool B μ u) k (q.source.indexedTree q.start q.reserve) →
    bandGapPrefixPower B μ u k q ≤ splitCoefficient*throughSum (rootGain (cappedStep μ B)) k q.source+
      splitCoefficient*bandTolerance u*throughSum (fun t => |rootGain (cappedStep μ B) t|) k q.source+
      16*splitCoefficient*Real.exp (-u/100)*(2:ℝ)^k := by
  filter_upwards [eventually_band_good_unit_power] with u H
  intro κ B cap μ critical h q k S hq hGood
  have hSub := indexedTree_subtree_labels hq
  have hPoint : ∀ b ∈ depthPrefixLabels k (q.source.indexedTree q.start q.reserve),
      normalizedNodeDecrease (cappedStep μ B) (bandPad u) b ≤
      splitCoefficient*rootGain (cappedStep μ B) b.source+
      splitCoefficient*bandTolerance u*|rootGain (cappedStep μ B) b.source|+16*splitCoefficient*Real.exp (-u/100) := by
    intro b hb
    exact H κ B cap μ critical h b S (hSub.subset (depthPrefixLabels_mem _ _ hb)) (depthPrefixLabels_good _ _ _ hGood hb)
  have hSum := List.sum_le_sum hPoint
  simp only [List.sum_map_add,List.sum_map_mul_left,List.map_const',List.sum_replicate,nsmul_eq_mul,indexed_depth_prefix_sum] at hSum
  rw [indexed_depth_prefix_sum (fun t => |rootGain (cappedStep μ B) t|) k q.start q.reserve q.source] at hSum
  have hCount : ((depthPrefixLabels k (q.source.indexedTree q.start q.reserve)).length:ℝ) ≤ (2:ℝ)^k := by
    have hh := depthPrefixLabels_length_bound k (q.source.indexedTree q.start q.reserve)
    exact_mod_cast (show (depthPrefixLabels k (q.source.indexedTree q.start q.reserve)).length ≤ 2^k by omega)
  have hScale := mul_le_mul_of_nonneg_left hCount
    (show 0 ≤ 16*splitCoefficient*Real.exp (-u/100) by have hc := split_coefficient_positive; positivity)
  unfold bandGapPrefixPower
  linear_combination hSum+hScale

end
end StrongSilver
