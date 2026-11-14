-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.LinkedParentCharge
import StrongSilver.LinkedObservable
import StrongSilver.BandFollowingBad
import StrongSilver.BandIncompleteDepth

namespace StrongSilver
open ScheduleTree BinaryForest Real Filter Set MeasureTheory
noncomputable section
set_option maxHeartbeats 6000000

def bandUnavailableIndicator (B μ u : ℝ) (q : ScheduleNode) : ℝ :=
  bandBadIndicator B μ u q+missingGoodChildIndicator (bandGoodBool B μ u) q

theorem bandUnavailableIndicator_nonnegative (B μ u : ℝ) (q : ScheduleNode) : 0 ≤ bandUnavailableIndicator B μ u q :=
  add_nonneg (bandBadIndicator_nonnegative B μ u q) (missingGoodChildIndicator_nonnegative _ q)

theorem band_unavailable_indicator_weight_sum (κ B μ u : ℝ) (h : List ℝ) :
    ((labels ((cartesian h).indexedTree 0 κ)).map fun q =>
      Real.exp (nu*nodePaddedHeight (cappedStep μ B) (bandPad u) q)*bandUnavailableIndicator B μ u q).sum =
    ((labels ((cartesian h).indexedTree 0 κ)).map fun q =>
      Real.exp (nu*nodePaddedHeight (cappedStep μ B) (bandPad u) q)*bandBadIndicator B μ u q).sum+
    ((parentedNodes 0 κ none (cartesian h)).map fun q => missingGoodChildWeight (bandGoodBool B μ u)
      (fun p => Real.exp (nu*nodePaddedHeight (cappedStep μ B) (bandPad u) p)) q.node).sum := by
  simp only [bandUnavailableIndicator,mul_add,List.sum_map_add]
  rw [indexed_missing_weight_sum (bandGoodBool B μ u) _ 0 κ none (cartesian h)]

theorem linkedParentObservable_integrable (φ : ℝ → ℝ) (P κ v a b : ℝ)
    (F : ScheduleNode → ℝ) (h : List ℝ) :
    IntervalIntegrable (linkedParentObservable φ P κ v F h) volume a b := by
  have hBase := linkedObservable_integrable (fun q => optionalNodeCharge F q.parent) φ 0 κ none none (cartesian h)
    (fun y => P+Real.exp y) (by fun_prop) a b
  have hWeighted := hBase.continuousOn_mul (show ContinuousOn (fun y : ℝ => Real.exp (v*y)) (uIcc a b) by fun_prop)
  have he : linkedParentObservable φ P κ v F h = fun y =>
      Real.exp (v*y)*linkedObservable (fun q => optionalNodeCharge F q.parent) φ 0 κ none none (cartesian h) (P+Real.exp y) := by
    funext y
    exact List.sum_map_mul_left _ _ _
  rw [he]
  exact hWeighted

/-- The parent/child exclusion cost in (4.25), including leaf gaps,
is paid by twice the actual unavailable-parent indicator. -/
theorem eventually_band_parent_exclusions : ∃ C > 0, ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ critical a b : ℝ, ∀ h : List ℝ,
    1 < κ → 1 < B → B ≤ cap → cap ≤ κ → B ≤ κ/128 → u ≤ firstAverageLogScale B →
    1/κ ≤ μ → μ ≤ 2/κ → μ*B ≤ 1/2 → a ≤ b →
    (∀ z ∈ h, 1-μ*z ≠ 0) → inverseChargeAbove (κ/4) h μ ≤ critical →
    critical ≤ 34*weightedCount h cap*cap^(-nu) → D κ h ≤ 1 →
    1 ≤ countAbove h B → κ^nu ≤ weightedCount h cap →
    (∫ y in a..b, linkedParentObservable (cappedStep μ B) (bandPad u) κ nu (bandUnavailableIndicator B μ u) h y) ≤
      C*weightedCount h cap*u^((9:ℝ)/10) := by
  obtain ⟨C,hC,H⟩ := eventually_band_unavailable_node_weight
  refine ⟨2*C/nu,by have hν := nu_positive; positivity,?_⟩
  filter_upwards [H] with u hBudget
  intro κ B cap μ critical a b h hκ hB hBcap hcapκ hBκ hU hμ hμu hμB hab hcrit hcritical hcriticalRank hD hcount hκW
  let φ := cappedStep μ B
  let P := bandPad u
  let F := bandUnavailableIndicator B μ u
  let xs := labels ((cartesian h).indexedTree 0 κ)
  have hDom := intervalIntegral.integral_mono_on hab
    (linkedParentObservable_integrable φ P κ nu a b F h)
    ((selectedNodeObservable_integrable φ P nu a b F xs).const_mul 2)
    (fun y _ => linkedParentObservable_upper φ P κ nu F (bandUnavailableIndicator_nonnegative B μ u) h y)
  rw [intervalIntegral.integral_const_mul] at hDom
  have hInt := selectedNodeObservable_integral_upper φ P nu a b F xs nu_positive.le
    (bandUnavailableIndicator_nonnegative B μ u) hab
  have hSum := hBudget κ B cap μ critical h hκ hB hBcap hcapκ hBκ hU hμ hμu hμB hcrit hcritical hcriticalRank hD hcount hκW
  have hWeighted : (xs.map fun q => Real.exp (nu*nodePaddedHeight φ P q)*F q).sum ≤
      C*weightedCount h cap*u^((9:ℝ)/10) := by
    dsimp only [xs,F,φ,P]
    rw [band_unavailable_indicator_weight_sum,band_bad_indicator_weight_sum]
    exact hSum
  have hFinal : nu*(∫ y in a..b, linkedParentObservable φ P κ nu F h y) ≤
      2*C*weightedCount h cap*u^((9:ℝ)/10) := by
    have hScale := mul_le_mul_of_nonneg_left hDom nu_positive.le
    linear_combination hScale+2*hInt+2*hWeighted
  calc
    _ ≤ (2*C*weightedCount h cap*u^((9:ℝ)/10))/nu := (le_div_iff₀ nu_positive).mpr (by linear_combination hFinal)
    _ = (2*C/nu)*weightedCount h cap*u^((9:ℝ)/10) := by ring

end
end StrongSilver
