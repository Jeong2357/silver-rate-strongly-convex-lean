-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandUnitGainBudget
import StrongSilver.BandGoodNode
import StrongSilver.BandGoodChildGeometry
import StrongSilver.GoodDepthTransport

namespace StrongSilver
open ScheduleTree BinaryForest Real Filter Set
noncomputable section
set_option maxHeartbeats 6500000

def bandGoodScore (B μ u : ℝ) (F : ScheduleNode → ℝ) (q : ScheduleNode) : ℝ :=
  if bandGoodBool B μ u q then F q else 0

theorem bandGoodScore_nonnegative (B μ u : ℝ) (F : ScheduleNode → ℝ) (hF : ∀ q, 0 ≤ F q) (q : ScheduleNode) :
    0 ≤ bandGoodScore B μ u F q := by unfold bandGoodScore; split_ifs; exact hF q; exact le_rfl

/-- Good source occurrences are a subfamily of the actual balanced
protected occurrences, preserving their original positions. -/
theorem band_good_score_sum_le_balanced (κ B μ u : ℝ) (h : List ℝ) (F : ScheduleNode → ℝ) (hF : ∀ q, 0 ≤ F q) :
    ((labels ((cartesian h).indexedTree 0 κ)).map fun q =>
      Real.exp (nu*nodePaddedHeight (cappedStep μ B) (bandPad u) q)*bandGoodScore B μ u F q).sum ≤
    ((bandBalancedNodes κ B μ u h).map fun q =>
      Real.exp (nu*parentedHeight (cappedStep μ B) (bandPad u) q)*F q.node).sum := by
  classical
  rw [← parentedNodes_erase]
  simp only [List.map_map,Function.comp_def]
  unfold bandBalancedNodes
  rw [bandProtectedNodes_eq,List.filter_filter,list_filter_sum_eq]
  apply List.sum_le_sum
  intro q hq
  by_cases hg : bandGoodBool B μ u q.node = true
  · obtain ⟨hGood,hPred⟩ := (bandGoodBool_iff B μ u q.node).mp hg
    have hBal := paddedGood_balanced hGood
    simp only [bandGoodScore,hg,↓reduceIte,decide_eq_true hPred,decide_eq_true hBal,Bool.true_and]
    rfl
  · simp only [bandGoodScore,if_neg hg,mul_zero]
    split_ifs
    · exact mul_nonneg (Real.exp_pos _).le (hF q.node)
    · exact le_rfl

/-- Original weighted absolute offset-one gains on good vertices have
an O(W) budget; all source assumptions are discharged by (4.17). -/
theorem eventually_band_good_gain_budget : ∃ C > 0, ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ critical : ℝ, ∀ h : List ℝ,
    1 < κ → 1 < B → B ≤ cap → cap ≤ κ → B ≤ κ/128 → u ≤ firstAverageLogScale B →
    1/κ ≤ μ → μ ≤ 2/κ → μ*B ≤ 1/2 →
    (∀ z ∈ h, 1-μ*z ≠ 0) → inverseChargeAbove (κ/4) h μ ≤ critical →
    critical ≤ 34*weightedCount h cap*cap^(-nu) → D κ h ≤ 1 →
    1 ≤ countAbove h B → κ^nu ≤ weightedCount h cap →
    ((labels ((cartesian h).indexedTree 0 κ)).map fun q =>
      Real.exp (nu*nodePaddedHeight (cappedStep μ B) (bandPad u) q)*
        bandGoodScore B μ u (fun q => |rootGain (cappedStep μ B) q.source|) q).sum ≤ C*weightedCount h cap := by
  obtain ⟨C,hC,H⟩ := eventually_band_unit_gain_budget
  refine ⟨C,hC,?_⟩
  filter_upwards [H] with u hBudget
  intro κ B cap μ critical h hκ hB hBcap hcapκ hBκ hU hμ hμu hμB hcrit hcritical hcriticalRank hD hcount hκW
  exact (band_good_score_sum_le_balanced κ B μ u h (fun q => |rootGain (cappedStep μ B) q.source|)
    (fun _ => abs_nonneg _)).trans
    (hBudget κ B cap μ critical h hκ hB hBcap hcapκ hBκ hU hμ hμu hμB hcrit hcritical hcriticalRank hD hcount hκW)

/-- The original weighted drawdown ratios on good vertices also have
an O(W) budget, paid by their actual nonnegative split excesses. -/
theorem eventually_band_good_drawdown_budget : ∃ C > 0, ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ critical : ℝ, ∀ h : List ℝ,
    1 < κ → 1 < B → B ≤ cap → cap ≤ κ → u ≤ firstAverageLogScale B →
    1/κ ≤ μ → μ ≤ 2/κ → μ*B ≤ 1/2 →
    (∀ z ∈ h, 1-μ*z ≠ 0) → inverseChargeAbove (κ/4) h μ ≤ critical →
    critical ≤ 34*weightedCount h cap*cap^(-nu) → D κ h ≤ 1 →
    1 ≤ countAbove h B → κ^nu ≤ weightedCount h cap →
    ((labels ((cartesian h).indexedTree 0 κ)).map fun q =>
      Real.exp (nu*nodePaddedHeight (cappedStep μ B) (bandPad u) q)*
        bandGoodScore B μ u (fun q => nodeLeftDrawdown (cappedStep μ B) q.source/
          (cappedStep μ B q.pivot-bandPad u)) q).sum ≤ C*weightedCount h cap := by
  classical
  obtain ⟨cd,hcd,hDraw⟩ := node_drawdown_charge
  let C := bandExcessConstant/cd
  have hC : 0 < C := div_pos bandExcessConstant_positive hcd
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_band_integral_estimates,eventually_band_forest_spacing] with u hInt hTol
  intro κ B cap μ critical h hκ hB hBcap hcapκ hU hμ hμu hμB hcrit hcritical hcriticalRank hD hcount hκW
  let φ := cappedStep μ B
  let P := bandPad u
  let w := fun q : ScheduleNode => Real.exp (nu*nodePaddedHeight φ P q)
  let F := fun q : ScheduleNode => nodeLeftDrawdown φ q.source/(φ q.pivot-P)
  let E := fun q : ScheduleNode => nodeExcess φ P (q.source,q.reserve)
  have hμ0 := (one_div_pos.mpr (zero_lt_one.trans hκ)).trans_le hμ
  have hzero : φ 0 ≤ 0 := by simp only [φ,cappedStep,if_pos (zero_lt_one.trans hB).le,logarithmicStep_zero,le_refl]
  have hIntActual := hInt κ B cap μ critical h hκ hB hBcap hcapκ hU hμ hμu hμB hcrit hcritical hcriticalRank hD hcount hκW
  have hEx := protected_excess_le_window (φ:=φ) (P:=P) (a:=outerBandLow u) (b:=outerBandHigh u)
    (Real.exp_pos _) (zero_lt_one.trans hκ).le hzero (bandEligible μ B u) (cartesian h)
  rw [band_windowNodeExcess_sum (zero_lt_one.trans hκ).le (zero_lt_one.trans hB).le] at hEx
  have hExBound := hEx.trans hIntActual.excess_upper
  have hPoint : ∀ q ∈ parentedNodes 0 κ none (cartesian h),
      cd*(w q.node*bandGoodScore B μ u F q.node) ≤
      if bandProtectedPredicate B μ u q.node then E q.node else 0 := by
    intro q hq
    by_cases hg : bandGoodBool B μ u q.node = true
    · obtain ⟨hGood,hPred⟩ := (bandGoodBool_iff B μ u q.node).mp hg
      have hb := paddedGood_balanced hGood
      have hc := hDraw φ P q.node.reserve (bandTolerance u) q.node.source (Real.exp_pos _)
        (parentedNodes_reserve_nonnegative (zero_lt_one.trans hκ).le hq) hzero hPred.1
        (hTol.2.1.trans (by norm_num)) hb
      simpa only [bandGoodScore,hg,if_pos hPred,↓reduceIte,w,F,E,nodePaddedHeight,nodeHeight,ScheduleNode.pivot,mul_assoc] using hc
    · simp only [bandGoodScore,if_neg hg,mul_zero]
      by_cases hp : bandProtectedPredicate B μ u q.node
      · rw [if_pos hp]
        exact nodeExcess_nonnegative φ (Real.exp_pos _) (parentedNodes_reserve_nonnegative (zero_lt_one.trans hκ).le hq)
          hzero q.node.source hp.1
      · rw [if_neg hp]
  have hSum := List.sum_le_sum hPoint
  have hErase := congrArg (fun qs : List ScheduleNode => (qs.map fun q => w q*bandGoodScore B μ u F q).sum)
    (parentedNodes_erase 0 κ none (cartesian h))
  simp only [List.map_map,Function.comp_def] at hErase
  rw [List.sum_map_mul_left,hErase] at hSum
  have hProtectedEq : ((parentedNodes 0 κ none (cartesian h)).map fun q =>
      if bandProtectedPredicate B μ u q.node then E q.node else 0).sum =
      ((bandProtectedNodes κ B μ u h).map fun q => E q.node).sum := by
    rw [bandProtectedNodes_eq,list_filter_sum_eq]
    simp only [decide_eq_true_eq]
  rw [hProtectedEq] at hSum
  dsimp only [C]
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hcd).mpr
  change ((bandProtectedNodes κ B μ u h).map fun q => E q.node).sum ≤ bandExcessConstant*weightedCount h cap at hExBound
  dsimp only [w,F,E,φ,P] at hSum hExBound ⊢
  linear_combination hSum+hExBound

end
end StrongSilver
