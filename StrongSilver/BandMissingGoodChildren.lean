-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BadChildEdgeSum

namespace StrongSilver
open ScheduleTree Real Filter
noncomputable section
set_option maxHeartbeats 5200000

local instance bandMissingDecidableGood (φ : ℝ → ℝ) (P κ δ : ℝ) (t : ScheduleTree) : Decidable (PaddedGood φ P κ δ t) := Classical.propDecidable _

/-- The missing-good-child part of (4.23), with all near/far/strip
budgets discharged for the actual stable signed schedule. -/
theorem eventually_band_missing_good_children : ∃ C > 0, ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ critical : ℝ, ∀ h : List ℝ,
    1 < κ → 1 < B → B ≤ cap → cap ≤ κ → B ≤ κ/128 → u ≤ firstAverageLogScale B →
    1/κ ≤ μ → μ ≤ 2/κ → μ*B ≤ 1/2 →
    (∀ b ∈ h, 1-μ*b ≠ 0) → inverseChargeAbove (κ/4) h μ ≤ critical →
    critical ≤ 34*weightedCount h cap*cap^(-nu) → D κ h ≤ 1 →
    1 ≤ countAbove h B → κ^nu ≤ weightedCount h cap →
    ((parentedNodes 0 κ none (cartesian h)).map fun q =>
      missingGoodChildWeight (bandGoodBool B μ u)
        (fun p => Real.exp (nu*nodePaddedHeight (cappedStep μ B) (bandPad u) p)) q.node).sum ≤
      C*weightedCount h cap*u^((9:ℝ)/10) := by
  obtain ⟨Cf,hCf,Hf⟩ := eventually_band_far_children_sum
  obtain ⟨Cn,hCn,Hn⟩ := eventually_band_near_bad_child_rate
  refine ⟨4+Cf+Cn,by positivity,?_⟩
  filter_upwards [Hf,Hn,eventually_band_lower_strip_weight,eventually_band_good_parent_geometry,
    eventually_band_all_good_children_internal,eventually_ge_atTop (1:ℝ)] with u hFar hNear hStrip hGeometry hInternal hu
  intro κ B cap μ critical h hκ hB hBcap hcapκ hBκ hU hμ hμu hμB hcrit hcritical hcriticalRank hD hcount hκW
  have hκ0 := zero_lt_one.trans hκ
  have hμ0 := (one_div_pos.mpr hκ0).trans_le hμ
  have hg (p : ScheduleNode) (hp : p ∈ BinaryForest.labels ((cartesian h).indexedTree 0 κ)) (hgood : bandGoodBool B μ u p = true) :=
    hGeometry κ B μ h p hκ0 hB hBκ hU hμ0 hμB hp hgood
  have hEdge := band_bad_child_edge_sum κ B μ u h hμ0 hμB (fun p hp hh => ⟨(hg p hp hh).1,(hg p hp hh).2.1⟩)
  have hS := hStrip κ B cap μ h hB hBcap hU hμ0 hμB
  have hF := hFar κ B cap μ h hB hBcap hU hμ0 hμB
  have hN := hNear κ B cap μ critical h hκ hB hBcap hcapκ hU hμ hμu hμB hcrit hcritical hcriticalRank hD hcount hκW
  have hI := hInternal κ B μ h hκ0 hB hBκ hU hμ0 hμB
  let w := fun p : ScheduleNode => Real.exp (nu*nodePaddedHeight (cappedStep μ B) (bandPad u) p)
  have hMissing := missing_good_child_weight_sum (bandGoodBool B μ u) w (fun p => (Real.exp_pos _).le) 0 κ none (cartesian h) hI
  have hz : rootBadEdgeWeight (bandGoodBool B μ u) w 0 κ none (cartesian h) = 0 := by cases cartesian h <;> rfl
  rw [hz,sub_zero] at hMissing
  have hPstrip := Real.rpow_le_rpow_of_exponent_le hu (by norm_num : (2:ℝ)/5 ≤ 9/10)
  have hPnear := Real.rpow_le_rpow_of_exponent_le hu (by norm_num : (3:ℝ)/5 ≤ 9/10)
  have hW := weightedCount_nonneg h cap
  have hRs := mul_le_mul_of_nonneg_left hPstrip (show 0 ≤ 4*weightedCount h cap by positivity)
  have hRn := mul_le_mul_of_nonneg_left hPnear (mul_nonneg hCn.le hW)
  change _ ≤ (4+Cf+Cn)*weightedCount h cap*u^((9:ℝ)/10)
  change _ ≤ _ at hMissing
  dsimp only [bandBinWidth] at hEdge hF
  dsimp only [w] at hMissing
  linear_combination (norm := (ring_nf; exact sub_nonpos.mpr le_rfl)) hMissing+hEdge+2*hS+hF+hN+hRs+hRn

/-- The complete bad-or-missing-child weight estimate (4.23). The
first sum counts bad vertices in the protected band; the second counts
good vertices whose left or right child is outside the good band. -/
theorem eventually_band_unavailable_node_weight : ∃ C > 0, ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ critical : ℝ, ∀ h : List ℝ,
    1 < κ → 1 < B → B ≤ cap → cap ≤ κ → B ≤ κ/128 → u ≤ firstAverageLogScale B →
    1/κ ≤ μ → μ ≤ 2/κ → μ*B ≤ 1/2 →
    (∀ b ∈ h, 1-μ*b ≠ 0) → inverseChargeAbove (κ/4) h μ ≤ critical →
    critical ≤ 34*weightedCount h cap*cap^(-nu) → D κ h ≤ 1 →
    1 ≤ countAbove h B → κ^nu ≤ weightedCount h cap →
    ((bandProtectedNodes κ B μ u h).map fun q =>
      if @PaddedGood (cappedStep μ B) (bandPad u) q.node.reserve (bandTolerance u) q.node.source then 0 else
        Real.exp (nu*parentedHeight (cappedStep μ B) (bandPad u) q)).sum+
    ((parentedNodes 0 κ none (cartesian h)).map fun q =>
      missingGoodChildWeight (bandGoodBool B μ u)
        (fun p => Real.exp (nu*nodePaddedHeight (cappedStep μ B) (bandPad u) p)) q.node).sum ≤
      C*weightedCount h cap*u^((9:ℝ)/10) := by
  classical
  obtain ⟨Cb,hCb,Hb⟩ := eventually_band_bad_weight_rate
  obtain ⟨Cm,hCm,Hm⟩ := eventually_band_missing_good_children
  refine ⟨Cb+Cm,add_pos hCb hCm,?_⟩
  filter_upwards [Hb,Hm,eventually_ge_atTop (1:ℝ)] with u hBad hMissing hu
  intro κ B cap μ critical h hκ hB hBcap hcapκ hBκ hU hμ hμu hμB hcrit hcritical hcriticalRank hD hcount hκW
  have h1 := hBad κ B cap μ critical h hκ hB hBcap hcapκ hU hμ hμu hμB hcrit hcritical hcriticalRank hD hcount hκW
  have h2 := hMissing κ B cap μ critical h hκ hB hBcap hcapκ hBκ hU hμ hμu hμB hcrit hcritical hcriticalRank hD hcount hκW
  have hPower := Real.rpow_le_rpow_of_exponent_le hu (by norm_num : (1:ℝ)/5 ≤ 9/10)
  have hScale := mul_le_mul_of_nonneg_left hPower (mul_nonneg hCb.le (weightedCount_nonneg h cap))
  linear_combination h1+h2+hScale

end
end StrongSilver
