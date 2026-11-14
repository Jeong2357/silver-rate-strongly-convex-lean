-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.LinkedFollowingIntegral
import StrongSilver.BandMissingGoodChildren

namespace StrongSilver
open ScheduleTree BinaryForest Real Filter Set MeasureTheory
noncomputable section
set_option maxHeartbeats 5800000

local instance bandFollowingGoodDecidable (φ : ℝ → ℝ) (P κ δ : ℝ) (t : ScheduleTree) :
    Decidable (PaddedGood φ P κ δ t) := Classical.propDecidable _

def bandBadIndicator (B μ u : ℝ) (q : ScheduleNode) : ℝ := by
  classical
  exact if bandProtectedPredicate B μ u q ∧ ¬ PaddedGood (cappedStep μ B) (bandPad u) q.reserve (bandTolerance u) q.source then 1 else 0

theorem bandBadIndicator_nonnegative (B μ u : ℝ) (q : ScheduleNode) : 0 ≤ bandBadIndicator B μ u q := by
  classical
  unfold bandBadIndicator
  split_ifs <;> norm_num

theorem band_bad_indicator_weight_sum (κ B μ u : ℝ) (h : List ℝ) :
    ((labels ((cartesian h).indexedTree 0 κ)).map fun q =>
      Real.exp (nu*nodePaddedHeight (cappedStep μ B) (bandPad u) q)*bandBadIndicator B μ u q).sum =
    ((bandProtectedNodes κ B μ u h).map fun q =>
      if PaddedGood (cappedStep μ B) (bandPad u) q.node.reserve (bandTolerance u) q.node.source then 0 else
        Real.exp (nu*parentedHeight (cappedStep μ B) (bandPad u) q)).sum := by
  classical
  rw [← parentedNodes_erase 0 κ none (cartesian h),List.map_map,bandProtectedNodes_eq,list_filter_sum_eq]
  congr 1
  apply List.map_congr_left
  intro q _
  simp only [Function.comp_def,decide_eq_true_eq,bandBadIndicator]
  by_cases hp : bandProtectedPredicate B μ u q.node <;>
    by_cases hg : PaddedGood (cappedStep μ B) (bandPad u) q.node.reserve (bandTolerance u) q.node.source <;>
    simp [hp,hg,parentedHeight,nodePaddedHeight]

/-- The following-pivot bad-vertex exclusion in (4.25), with its full
cutoff integral paid by the actual (4.13) bad-vertex weight budget. -/
theorem eventually_band_following_bad : ∃ C > 0, ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ critical a b : ℝ, ∀ h : List ℝ,
    1 < κ → 1 < B → B ≤ cap → cap ≤ κ → u ≤ firstAverageLogScale B →
    1/κ ≤ μ → μ ≤ 2/κ → μ*B ≤ 1/2 → a ≤ b →
    (∀ z ∈ h, 1-μ*z ≠ 0) → inverseChargeAbove (κ/4) h μ ≤ critical →
    critical ≤ 34*weightedCount h cap*cap^(-nu) → D κ h ≤ 1 →
    1 ≤ countAbove h B → κ^nu ≤ weightedCount h cap →
    (∫ y in a..b, linkedFollowingObservable (cappedStep μ B) (bandPad u) κ nu (bandBadIndicator B μ u) h y) ≤
      C*weightedCount h cap*u^((1:ℝ)/5) := by
  obtain ⟨C,hC,H⟩ := eventually_band_bad_weight_rate
  refine ⟨C/nu,div_pos hC nu_positive,?_⟩
  filter_upwards [H] with u hBad
  intro κ B cap μ critical a b h hκ hB hBcap hcapκ hU hμ hμu hμB hab hcrit hcritical hcriticalRank hD hcount hκW
  have hμ0 := (one_div_pos.mpr (zero_lt_one.trans hκ)).trans_le hμ
  have hφ := cappedStep_monotone (B:=B) hμ0 (by linarith only [hμB])
  have hIntegral := linkedFollowingObservable_integral_upper (cappedStep μ B) hφ (bandPad u) κ nu a b
    (bandBadIndicator B μ u) h nu_positive.le (bandBadIndicator_nonnegative B μ u) hab
  rw [band_bad_indicator_weight_sum] at hIntegral
  have hBnd := hBad κ B cap μ critical h hκ hB hBcap hcapκ hU hμ hμu hμB hcrit hcritical hcriticalRank hD hcount hκW
  have hFinal := hIntegral.trans hBnd
  calc
    _ ≤ (C*weightedCount h cap*u^((1:ℝ)/5))/nu := (le_div_iff₀ nu_positive).mpr (by linear_combination hFinal)
    _ = (C/nu)*weightedCount h cap*u^((1:ℝ)/5) := by ring

end
end StrongSilver
