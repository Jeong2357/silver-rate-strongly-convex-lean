-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandVisibilityEstimates
import StrongSilver.BandNodeWeightBudget
import StrongSilver.ShortBalancedEdges

namespace StrongSilver
open ScheduleTree Real Filter Set
noncomputable section
set_option maxHeartbeats 4800000

def bandVisibilityConstant : ℝ := nu*bandIntegralConstant/visibilityWindowFactor nu visibilitySpacing+9600

theorem bandVisibilityConstant_positive : 0 < bandVisibilityConstant := by
  have hF := visibilityWindowFactor_positive nu_positive visibilitySpacing_positive
  have hI := bandIntegralConstant_positive
  have hν := nu_positive
  unfold bandVisibilityConstant
  positivity

/-- The total weight of the long visible occurrence list is bounded by
the same original-word rank budget. -/
theorem band_long_weight_le_all (κ B μ u s : ℝ) (h : List ℝ) :
    ((bandLongVisibleNodes κ B μ u s h).map fun q => Real.exp (nu*parentedHeight (cappedStep μ B) (bandPad u) q)).sum ≤
      ((parentedNodes 0 κ none (cartesian h)).map fun q => bandPivotWeight B μ u q.node.pivot).sum := by
  classical
  let w := fun q : ParentedScheduleNode => bandPivotWeight B μ u q.node.pivot
  have he : ((bandLongVisibleNodes κ B μ u s h).map fun q => Real.exp (nu*parentedHeight (cappedStep μ B) (bandPad u) q)).sum =
      ((bandLongVisibleNodes κ B μ u s h).map w).sum := by
    congr 1
    apply List.map_congr_left
    intro q hq
    have hh := of_decide_eq_true (List.mem_filter.mp hq).2
    have he : bandEligible μ B u 0 q.node.pivot = true := by
      simpa only [bandEligible] using hh.2.1
    dsimp only [w,bandPivotWeight]
    rw [if_pos he]
    rfl
  rw [he]
  have hsub : (bandLongVisibleNodes κ B μ u s h).Sublist (parentedNodes 0 κ none (cartesian h)) := List.filter_sublist
  apply (hsub.map w).sum_le_sum
  intro x hx
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hx
  exact bandPivotWeight_nonnegative B μ u q.node.pivot

/-- Removing the one-pivot price costs only an absolute multiple of W.
The remaining sum controls both the positive logarithmic gains and the
full signed-gap positive-sum deficits. -/
theorem eventually_band_long_gain_budget : ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ critical : ℝ, ∀ h : List ℝ,
    1 < κ → 1 < B → B ≤ cap → cap ≤ κ → u ≤ firstAverageLogScale B →
    1/κ ≤ μ → μ ≤ 2/κ → μ*B ≤ 1/2 →
    (∀ b ∈ h, 1-μ*b ≠ 0) → inverseChargeAbove (κ/4) h μ ≤ critical →
    critical ≤ 34*weightedCount h cap*cap^(-nu) → D κ h ≤ 1 →
    1 ≤ countAbove h B → κ^nu ≤ weightedCount h cap →
    ((bandLongVisibleNodes κ B μ u visibilitySpacing h).map fun q =>
      Real.exp (nu*parentedHeight (cappedStep μ B) (bandPad u) q)*
        (max (paddedRootGain (cappedStep μ B) (bandPad u) q.node.reserve q.node.source) 0+
          gapLogDeficit (cappedStep μ B) (bandPad u) q.node.reserve q.node.source.word)).sum ≤
      bandVisibilityConstant*weightedCount h cap := by
  classical
  filter_upwards [eventually_band_visibility_estimates,eventually_band_node_weight_budget,eventually_gt_atTop (0:ℝ)]
    with u hVis hWeight hu
  intro κ B cap μ critical h hκ hB hBcap hcapκ hU hμ hμu hμB hcrit hcritical hcriticalRank hD hcount hκW
  have hμ0 := (one_div_pos.mpr (zero_lt_one.trans hκ)).trans_le hμ
  have H := hVis κ B cap μ critical visibilitySpacing h hκ hB hBcap hcapκ hU hμ hμu hμB
    visibilitySpacing_positive.le hcrit hcritical hcriticalRank hD hcount hκW
  let qs := bandLongVisibleNodes κ B μ u visibilitySpacing h
  let w := fun q => Real.exp (nu*parentedHeight (cappedStep μ B) (bandPad u) q)
  let S := fun q : ParentedScheduleNode => visibleNodeScore (cappedStep μ B) (bandPad u) (2400/u) (bandEligible μ B u) q.node
  let G := fun q : ParentedScheduleNode => max (paddedRootGain (cappedStep μ B) (bandPad u) q.node.reserve q.node.source) 0+
    gapLogDeficit (cappedStep μ B) (bandPad u) q.node.reserve q.node.source.word
  have hprice : 0 ≤ 2400/u := by positivity
  have hpoint : ∀ q ∈ qs, w q*G q ≤ w q*S q+(2400/u)*w q := by
    intro q hq
    have hh := of_decide_eq_true (List.mem_filter.mp hq).2
    have hscore : S q = max (paddedRootGain (cappedStep μ B) (bandPad u) q.node.reserve q.node.source-2400/u) 0+
        gapLogDeficit (cappedStep μ B) (bandPad u) q.node.reserve q.node.source.word := if_pos ⟨hh.1,hh.2.1⟩
    have hmax : max (paddedRootGain (cappedStep μ B) (bandPad u) q.node.reserve q.node.source) 0 ≤
        max (paddedRootGain (cappedStep μ B) (bandPad u) q.node.reserve q.node.source-2400/u) 0+2400/u := by
      apply max_le
      · linarith only [le_max_left (paddedRootGain (cappedStep μ B) (bandPad u) q.node.reserve q.node.source-2400/u) (0:ℝ)]
      · linarith only [le_max_right (paddedRootGain (cappedStep μ B) (bandPad u) q.node.reserve q.node.source-2400/u) (0:ℝ),hprice]
    have hi := mul_le_mul_of_nonneg_left hmax (Real.exp_pos (nu*parentedHeight (cappedStep μ B) (bandPad u) q)).le
    rw [hscore]
    dsimp only [G,w]
    linear_combination hi
  have hsum := List.sum_le_sum hpoint
  rw [List.sum_map_add,List.sum_map_mul_left] at hsum
  have hw := (band_long_weight_le_all κ B μ u visibilitySpacing h).trans (hWeight κ B cap μ h hB hBcap hU hμ0 hμB)
  have hp := mul_le_mul_of_nonneg_left hw hprice
  have hcost : (2400/u)*(4*weightedCount h cap*u) = 9600*weightedCount h cap := by field_simp [hu.ne'] <;> ring
  rw [hcost] at hp
  have hF := visibilityWindowFactor_positive nu_positive visibilitySpacing_positive
  have hscore : (qs.map fun q => w q*S q).sum ≤ (nu*bandIntegralConstant/visibilityWindowFactor nu visibilitySpacing)*weightedCount h cap := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hF).mpr
    linear_combination H
  change (qs.map fun q => w q*G q).sum ≤ _
  unfold bandVisibilityConstant
  linear_combination hsum+hp+hscore

end
end StrongSilver
