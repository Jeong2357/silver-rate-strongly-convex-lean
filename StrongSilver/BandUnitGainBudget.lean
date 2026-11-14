-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandAbsoluteGainBudget
import StrongSilver.BandUnitPointwise
import StrongSilver.BandBadWeightRate

namespace StrongSilver
open ScheduleTree Real Filter
noncomputable section
set_option maxHeartbeats 6800000

local instance (φ : ℝ → ℝ) (P κ δ : ℝ) (t : ScheduleTree) : Decidable (PaddedBalanced φ P κ δ t) := Classical.propDecidable _

def bandBalancedNodes (κ B μ u : ℝ) (h : List ℝ) : List ParentedScheduleNode :=
  (bandProtectedNodes κ B μ u h).filter fun q => decide
    (PaddedBalanced (cappedStep μ B) (bandPad u) q.node.reserve (bandTolerance u) q.node.source)

/-- The offset-one absolute gain sum in (4.17) for the actual original
balanced vertices. All drawdown, cut-gain and pad-error sums are paid by
the previously proved source-schedule budgets. -/
theorem eventually_band_unit_gain_budget : ∃ C > 0, ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ critical : ℝ, ∀ h : List ℝ,
    1 < κ → 1 < B → B ≤ cap → cap ≤ κ → B ≤ κ/128 → u ≤ firstAverageLogScale B →
    1/κ ≤ μ → μ ≤ 2/κ → μ*B ≤ 1/2 →
    (∀ b ∈ h, 1-μ*b ≠ 0) → inverseChargeAbove (κ/4) h μ ≤ critical →
    critical ≤ 34*weightedCount h cap*cap^(-nu) → D κ h ≤ 1 →
    1 ≤ countAbove h B → κ^nu ≤ weightedCount h cap →
    ((bandBalancedNodes κ B μ u h).map fun q =>
      Real.exp (nu*parentedHeight (cappedStep μ B) (bandPad u) q)*|rootGain (cappedStep μ B) q.node.source|).sum ≤
      C*weightedCount h cap := by
  classical
  obtain ⟨Ca,hCa,hAbsolute⟩ := eventually_band_absolute_gain_budget
  obtain ⟨cd,hcd,hdraw⟩ := node_drawdown_charge
  let C := Ca+2*bandExcessConstant/cd+32
  have hC : 0 < C := by have hE := bandExcessConstant_positive; dsimp only [C]; positivity
  have ht := tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/10)
  refine ⟨C,hC,?_⟩
  filter_upwards [hAbsolute,eventually_band_integral_estimates,eventually_band_unit_pointwise,
    eventually_band_node_weight_budget,eventually_exp_negative_linear_le_inverse (by norm_num : (0:ℝ) < 1/100),
    eventually_gt_atTop (0:ℝ),ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/4))]
    with u hAbs hInt hUnit hWeight hExp hu hTolerance
  intro κ B cap μ critical h hκ hB hBcap hcapκ hBκ hU hμ hμu hμB hcrit hcritical hcriticalRank hD hcount hκW
  have hκ0 := zero_lt_one.trans hκ
  have hB0 := zero_lt_one.trans hB
  have hμ0 := (one_div_pos.mpr hκ0).trans_le hμ
  have hzero : cappedStep μ B 0 ≤ 0 := by simp only [cappedStep,if_pos hB0.le,logarithmicStep_zero,le_refl]
  have hδ : 0 < bandTolerance u := Real.rpow_pos_of_pos hu _
  have hδmax : bandTolerance u ≤ 1/4 := by simpa only [bandTolerance,neg_div] using hTolerance.le
  have HA := hAbs κ B cap μ critical h hκ hB hBcap hcapκ hU hμ hμu hμB hcrit hcritical hcriticalRank hD hcount hκW
  have HI := hInt κ B cap μ critical h hκ hB hBcap hcapκ hU hμ hμu hμB hcrit hcritical hcriticalRank hD hcount hκW
  let xs := bandProtectedNodes κ B μ u h
  let qs := bandBalancedNodes κ B μ u h
  let w := fun q : ParentedScheduleNode => Real.exp (nu*parentedHeight (cappedStep μ B) (bandPad u) q)
  let g := fun q : ParentedScheduleNode => paddedRootGain (cappedStep μ B) (bandPad u) q.node.reserve q.node.source
  let G := fun q : ParentedScheduleNode => rootGain (cappedStep μ B) q.node.source
  let E := fun q : ParentedScheduleNode => nodeExcess (cappedStep μ B) (bandPad u) (q.node.source,q.node.reserve)
  let d := fun q : ParentedScheduleNode => nodeLeftDrawdown (cappedStep μ B) q.node.source/(cappedStep μ B q.node.pivot-bandPad u)
  have hsub : qs.Sublist xs := List.filter_sublist
  have hprotected (q : ParentedScheduleNode) (hq : q ∈ qs) : q ∈ xs := (List.mem_filter.mp hq).1
  have hbalanced (q : ParentedScheduleNode) (hq : q ∈ qs) :
      PaddedBalanced (cappedStep μ B) (bandPad u) q.node.reserve (bandTolerance u) q.node.source :=
    of_decide_eq_true (List.mem_filter.mp hq).2
  have hEx : ∀ q ∈ xs, 0 ≤ E q := by
    intro q hq
    have hh := of_decide_eq_true (List.mem_filter.mp hq).2
    exact nodeExcess_nonnegative (cappedStep μ B) (Real.exp_pos _)
      (parentedNodes_reserve_nonnegative hκ0.le (List.mem_filter.mp hq).1) hzero q.node.source hh.1
  have hExSum := protected_excess_le_window (φ := cappedStep μ B) (P := bandPad u)
    (a := outerBandLow u) (b := outerBandHigh u) (Real.exp_pos _) hκ0.le hzero (bandEligible μ B u) (cartesian h)
  rw [band_windowNodeExcess_sum hκ0.le hB0.le] at hExSum
  have hEqSub : (qs.map E).sum ≤ (xs.map E).sum := (hsub.map E).sum_le_sum (by
    intro x hx
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hx
    exact hEx q hq)
  have hEqBudget : (qs.map E).sum ≤ bandExcessConstant*weightedCount h cap := hEqSub.trans (hExSum.trans HI.excess_upper)
  have hDrawPoint : ∀ q ∈ qs, cd*(w q*d q) ≤ E q := by
    intro q hq
    have hp := hprotected q hq
    have hh := of_decide_eq_true (List.mem_filter.mp hp).2
    have hd := hdraw (cappedStep μ B) (bandPad u) q.node.reserve (bandTolerance u) q.node.source
      (Real.exp_pos _) (parentedNodes_reserve_nonnegative hκ0.le (List.mem_filter.mp hp).1) hzero hh.1
      (hδmax.trans (by norm_num)) (hbalanced q hq)
    dsimp only [w,d,E,parentedHeight,ScheduleNode.pivot]
    linear_combination hd
  have hDraw := List.sum_le_sum hDrawPoint
  rw [List.sum_map_mul_left] at hDraw
  have hDrawBudget : (qs.map fun q => w q*d q).sum ≤ (bandExcessConstant/cd)*weightedCount h cap := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hcd).mpr
    linear_combination hDraw+hEqBudget
  have hAbsSub : (qs.map fun q => w q*|g q|).sum ≤ (xs.map fun q => w q*|g q|).sum := (hsub.map _).sum_le_sum (by
    intro x hx
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hx
    exact mul_nonneg (Real.exp_pos _).le (abs_nonneg _))
  have hAbsOther : 0 ≤ ((bandProtectedNodes κ B μ u h).map fun q =>
      |paddedRootDecrease (cappedStep μ B) (bandPad u) q.node.reserve q.node.source|).sum := List.sum_nonneg (by
    intro x hx
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hx
    exact abs_nonneg _)
  have hAbsBudget : (qs.map fun q => w q*|g q|).sum ≤ Ca*weightedCount h cap := by
    dsimp only [xs,w,g] at hAbsSub
    linarith only [HA,hAbsOther,hAbsSub]
  have hWMap : (qs.map w).sum = (qs.map fun q => bandPivotWeight B μ u q.node.pivot).sum := by
    congr 1
    apply List.map_congr_left
    intro q hq
    have hp := hprotected q hq
    have hh := of_decide_eq_true (List.mem_filter.mp hp).2
    have he : bandEligible μ B u 0 q.node.pivot = true := by simpa only [bandEligible] using hh.2.1
    dsimp only [bandPivotWeight,w,parentedHeight,nodeHeight,ScheduleNode.pivot]
    dsimp only [ScheduleNode.pivot] at he
    rw [if_pos he]
  have hsubAll : qs.Sublist (parentedNodes 0 κ none (cartesian h)) := hsub.trans List.filter_sublist
  have hWSub := (hsubAll.map (fun q => bandPivotWeight B μ u q.node.pivot)).sum_le_sum (by
    intro x hx
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hx
    exact bandPivotWeight_nonnegative B μ u q.node.pivot)
  rw [← hWMap] at hWSub
  have hWBound := hWSub.trans (hWeight κ B cap μ h hB hBcap hU hμ0 hμB)
  have hWNonneg : 0 ≤ (qs.map w).sum := List.sum_nonneg (by
    intro x hx
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hx
    exact (Real.exp_pos _).le)
  have hExp' : Real.exp (-u/100) ≤ 1/u := by simpa only [show -((1:ℝ)/100)*u = -u/100 by ring] using hExp
  have hError1 := mul_le_mul_of_nonneg_right hExp' hWNonneg
  have hError2 := mul_le_mul_of_nonneg_left hWBound (show (0:ℝ) ≤ 1/u by positivity)
  have hId : (1/u)*(4*weightedCount h cap*u) = 4*weightedCount h cap := by field_simp [hu.ne'] <;> ring
  rw [hId] at hError2
  have hError : 8*Real.exp (-u/100)*(qs.map w).sum ≤ 32*weightedCount h cap := by linear_combination 8*hError1+8*hError2
  have hpoint : ∀ q ∈ qs, w q*|G q| ≤ w q*|g q|+2*(w q*d q)+(8*Real.exp (-u/100))*w q := by
    intro q hq
    have huq := (hUnit κ B μ (bandTolerance u) h q hκ0 hB hBκ hU hμ0 hμB hδ.le hδmax (hprotected q hq) (hbalanced q hq)).2
    have hh := abs_sub_le (G q) (g q) (0:ℝ)
    simp only [sub_zero] at hh
    have hGain : |G q| ≤ |g q|+2*d q+8*Real.exp (-u/100) := by
      dsimp only [G,g,d]
      linear_combination hh+huq
    have hm := mul_le_mul_of_nonneg_left hGain (Real.exp_pos (nu*parentedHeight (cappedStep μ B) (bandPad u) q)).le
    dsimp only [w]
    linear_combination hm
  have hsum := List.sum_le_sum hpoint
  simp only [List.sum_map_add,List.sum_map_mul_left] at hsum
  change (qs.map fun q => w q*|G q|).sum ≤ _
  dsimp only [C]
  linear_combination hsum+hAbsBudget+2*hDrawBudget+hError

end
end StrongSilver
