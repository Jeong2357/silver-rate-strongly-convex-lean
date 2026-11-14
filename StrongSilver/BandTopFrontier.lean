-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FrozenFrontierCount
import StrongSilver.BandCutTrees
import StrongSilver.BandExcludedForest
import StrongSilver.FullCutPaddingRank

namespace StrongSilver
open ScheduleTree BinaryForest Real Filter Set
noncomputable section
set_option maxHeartbeats 5800000

theorem indexedFrontier_length_eq_cut (φ : ℝ → ℝ) (hφ : Monotone φ) (s : ℝ) (hzero : φ 0 ≤ s)
    (start : ℕ) (κ : ℝ) (t : ScheduleTree) (hc : t.Cartesian) :
    ((indexedFrontier φ s start κ t).length:ℝ) =
      (((cutScheduleFrom (fun _ b => decide (s < φ b)) start t.word).phases.length:ℝ)+1) := by
  have H := indexedFrontier_sum (fun _ _ _ => 1) φ hφ s hzero start κ t hc
  simpa only [gapObservable,List.map_const',List.sum_replicate,nsmul_eq_mul,mul_one] using H

/-- Weighted size of the actual top frontier, including its terminal
gap, is bounded by the original capped rank weight. -/
theorem eventually_band_top_frontier : ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ b : ℝ, ∀ h : List ℝ,
    1 < B → B ≤ cap → u ≤ firstAverageLogScale B → 0 < μ → μ*B ≤ 1/2 →
    b ∈ Icc (outerBandLow u) (outerBandHigh u) → 1 ≤ countAbove h B →
    Real.exp (nu*b)*((bandIndexedFrontier κ B μ u b h).length:ℝ) ≤ 4*weightedCount h cap := by
  filter_upwards [eventually_outer_band_log_window] with u hWindow
  intro κ B cap μ b h hB hBcap hU hμ hμB hb hcount
  let A := bandCutoff μ u b
  have W := hWindow B μ b hB hU hμ hμB hb
  have hsize := logarithmicCutoff_size hμ (show (0:ℝ) ≤ bandPad u by exact (Real.exp_pos _).le) W.2.1
  have hA : 0 < A := W.2.2.1
  have hη := firstAverageEta_bounds.1
  have hBpower : B^(1-firstAverageEta) ≤ B := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hB.le
      (show 1-firstAverageEta ≤ (1:ℝ) by linarith only [hη])
  have hAB : A ≤ B := W.2.2.2.2.2.2.2.2.1.trans hBpower
  have hCountA : 1 ≤ countAbove h A := hcount.trans (countAbove_antitone h hAB)
  have hRank := full_cut_gap_count_rank hA (hAB.trans hBcap) h hCountA
  have hφ := cappedStep_monotone (B:=B) hμ (by linarith only [hμB])
  have hzero : cappedStep μ B 0 ≤ bandPad u+Real.exp b := by
    rw [cappedStep,if_pos (zero_lt_one.trans hB).le,logarithmicStep_zero]
    exact add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  have hLength := indexedFrontier_length_eq_cut (cappedStep μ B) hφ (bandPad u+Real.exp b) hzero 0 κ (cartesian h) (cartesian_valid h)
  have hcut := band_heightCut_eq hμ (by linarith only [hμB]) W.2.2.2.2.2.2.2.2.2.2 h
  rw [cartesian_word] at hLength
  change ((bandIndexedFrontier κ B μ u b h).length:ℝ) = ((heightCut (cappedStep μ B) (bandPad u) b h).phases.length:ℝ)+1 at hLength
  rw [hcut] at hLength
  have hp := Real.exp_pos ((987:ℝ)/1000*u)
  change 0 < bandPad u at hp
  have hheight : Real.exp b ≤ 2*A := by dsimp only [A,bandCutoff]; linarith only [hsize.1,hp]
  have hNorm := height_power_normalization hA hheight
  rw [hLength]
  have hScale := mul_le_mul_of_nonneg_left hRank (Real.exp_pos (nu*b)).le
  have hCancel := mul_le_mul_of_nonneg_left hNorm (show 0 ≤ 2*weightedCount h cap by have hh := weightedCount_nonneg h cap; positivity)
  dsimp only [A,bandFullCut] at hScale ⊢
  linear_combination hScale+hCancel

end
end StrongSilver
