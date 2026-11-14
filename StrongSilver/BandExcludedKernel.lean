-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandKernelGapGain
import StrongSilver.BandExcludedSubperm
import StrongSilver.InnerBandKernelWindow

namespace StrongSilver
open ScheduleTree BinaryForest Real Filter Set
noncomputable section
set_option maxHeartbeats 6200000

/-- The excluded-gap kernel estimate applies to the exact occurrence
complement of available pair starts, with its original count. -/
theorem eventually_band_excluded_kernel : ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ critical y : ℝ, ∀ h : List ℝ, ∀ qs : List ScheduleNode,
    BandSourceData κ B cap μ critical u h → y ∈ Icc (innerBandLow u) (innerBandHigh u) →
    qs.Subperm (bandIndexedFrontier κ B μ u y h) →
    (qs.map (bandKernelGapPower B μ u y)).sum ≤
      2*splitCoefficient*bandRefinementSavings κ B μ u y h+
      (153600*splitCoefficient)*(2:ℝ)^fourPhaseDepth u/u*(qs.length:ℝ) := by
  filter_upwards [eventually_band_excluded_subperm,eventually_inner_band_kernel_window] with u hForest hGeometry
  intro κ B cap μ critical y h qs S hy hSub
  let d := fourPhaseDepth u
  let s := 1/Real.sqrt 2
  let a := 1-s
  have hs0 : 0 ≤ s := (one_div_pos.mpr (zero_lt_one.trans sqrt_two_bounds.1)).le
  have hs1 : s ≤ 1 := (one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1) sqrt_two_bounds.1.le).trans_eq (by norm_num)
  have ha0 : 0 ≤ a := sub_nonneg.mpr hs1
  have hGet (k : ℕ) (hk : k ≤ d+2) := hForest κ B μ y k h qs hSub (zero_lt_one.trans S.kappa_gt_one).le S.threshold_gt_one
    S.scale_upper S.mu_positive S.curvature_half (hGeometry y k hy hk).1 (hGeometry y k hy hk).2.1 hk
  have h0 := mul_le_mul_of_nonneg_left (hGet d (by omega)) ha0
  have h1 := hGet (d+1) (by omega)
  have h2 := mul_le_mul_of_nonneg_left (hGet (d+2) (by omega)) hs0
  unfold bandKernelGapPower
  rw [List.sum_map_add,List.sum_map_add,List.sum_map_mul_left,List.sum_map_mul_left]
  dsimp only [d,s,a] at h0 h1 h2
  linear_combination h0+h1+h2

end
end StrongSilver
