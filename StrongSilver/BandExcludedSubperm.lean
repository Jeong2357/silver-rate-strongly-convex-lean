-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandExcludedForest
import StrongSilver.FiniteSubpermSum

namespace StrongSilver
open ScheduleTree BinaryForest Real Filter Set
noncomputable section
set_option maxHeartbeats 5400000

/-- The excluded-forest bound applies to any subpermutation of original
frontier occurrences. This permits an exact complement of available
pair starts without assuming a measurable selection of reservations. -/
theorem eventually_band_excluded_subperm : ∀ᶠ u : ℝ in atTop,
    ∀ κ B μ y : ℝ, ∀ k : ℕ, ∀ h : List ℝ, ∀ qs : List ScheduleNode,
    qs.Subperm (bandIndexedFrontier κ B μ u y h) → 0 ≤ κ → 1 < B → u ≤ firstAverageLogScale B → 0 < μ → μ*B ≤ 1/2 →
    y ∈ Icc (outerBandLow u) (outerBandHigh u) →
    y-(k:ℝ)*Real.log rho ∈ Icc (outerBandLow u) (outerBandHigh u) → k ≤ fourPhaseDepth u+2 →
    (qs.map (bandGapWindowPower B μ u y k)).sum ≤
      splitCoefficient*bandRefinementSavings κ B μ u y h+
        ((76800*splitCoefficient)*(2:ℝ)^fourPhaseDepth u/u)*
          (qs.length:ℝ) := by
  filter_upwards [eventually_band_excluded_gap_power,eventually_outer_band_log_window] with u hGap hWindow
  intro κ B μ y k h qs hSub hκ hB hU hμ hμB hy hlow hk
  let xs := bandIndexedFrontier κ B μ u y h
  let R := fun q : ScheduleNode => gapSavingsMaximum (cappedStep μ B) (bandPad u) q.reserve (2400/u) q.start q.source.word (bandEligible μ B u)
  let M := (76800*splitCoefficient)*(2:ℝ)^fourPhaseDepth u/u
  have hzero : cappedStep μ B 0 ≤ bandPad u+Real.exp y := by
    rw [cappedStep,if_pos (zero_lt_one.trans hB).le,logarithmicStep_zero]
    exact add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  have hpoint : ∀ q ∈ qs, bandGapWindowPower B μ u y k q ≤ splitCoefficient*R q+M := by
    intro q hq
    have hf := hSub.subset hq
    exact hGap B μ q.reserve y q.start k q.source hB hU hμ hμB
      (indexedFrontier_reserve_nonnegative hκ hf) hy hlow hk
      (indexedFrontier_source_cartesian (cartesian_valid h) hf) (indexedFrontier_root_upper hzero hf)
  have hsum := List.sum_le_sum hpoint
  simp only [List.sum_map_add,List.sum_map_mul_left,List.map_const',List.sum_replicate,nsmul_eq_mul] at hsum
  have hRSub : (qs.map R).sum ≤ (xs.map R).sum := list_nonnegative_subperm_sum_le R hSub (by
    intro q hq
    exact gapSavingsMaximum_nonnegative _ _ _ _ _ _ _)
  have hRFront := indexedFrontier_savings (κ := κ) (cappedStep μ B)
    (cappedStep_monotone hμ (by linarith only [hμB])) hzero (2400/u) (bandEligible μ B u) (cartesian h) (cartesian_valid h)
  have hbranch := (hWindow B μ y hB hU hμ hμB hy).2.2.2.2.2.2.2.2.2.2
  have hCut := band_heightCut_eq hμ (by linarith only [hμB]) hbranch h
  rw [cartesian_word,hCut] at hRFront
  have hRUpper : (qs.map R).sum ≤ bandRefinementSavings κ B μ u y h := hRSub.trans_eq hRFront
  have hRC := mul_le_mul_of_nonneg_left hRUpper split_coefficient_positive.le
  change (qs.map (bandGapWindowPower B μ u y k)).sum ≤ _
  dsimp only [M] at hsum ⊢
  linear_combination hsum+hRC


end
end StrongSilver
