-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandCutoffLogDistance
import StrongSilver.InnerBandKernelWindow
import StrongSilver.SmoothedBandGeometry
import StrongSilver.BandSourceData

namespace StrongSilver
open ScheduleTree BinaryForest Real Filter Set
noncomputable section
set_option maxHeartbeats 7500000

/-- The inverse cutoff endpoints lie outside the two actual smoothing
windows, with room for the square-root height margins. -/
theorem eventually_band_smoothing_endpoints : ∀ᶠ u : ℝ in atTop,
    ∀ B μ : ℝ, 1 < B → u ≤ firstAverageLogScale B → 0 < μ → μ*B ≤ 1/2 →
    Real.log (bandCutoff μ u (innerBandLow u)) ≤ u/bandRatio ∧
    u+Real.sqrt u ≤ Real.log (bandCutoff μ u (innerBandHigh u)) := by
  filter_upwards [eventually_band_cutoff_log_distance,eventually_inner_band_kernel_window,eventually_inner_band_geometry,
    eventually_ge_atTop ((Real.log 2)^2)] with u hDistance hWindow hGeometry hu
  intro B μ hB hU hμ hμB
  have hLo := hDistance B μ (innerBandLow u) hB hU hμ hμB
    (hWindow (innerBandLow u) 0 ⟨le_rfl,hGeometry.2.2.1⟩ (by omega)).1
  have hHi := hDistance B μ (innerBandHigh u) hB hU hμ hμB
    (hWindow (innerBandHigh u) 0 ⟨hGeometry.2.2.1,le_rfl⟩ (by omega)).1
  have hLog2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
  have hSqrt : Real.log 2 ≤ Real.sqrt u := (Real.le_sqrt hLog2.le hGeometry.1.le).mpr hu
  have hLo' := (abs_le.mp hLo).2
  have hHi' := (abs_le.mp hHi).1
  dsimp only [innerBandLow,innerBandHigh] at hLo' hHi' ⊢
  constructor <;> linarith only [hLo',hHi',hSqrt]

/-- Every original positive pivot with a nonzero averaged threshold
weight lies below the original cap and in the protected height band.
This supplies the exact support statement used in (4.4). -/
theorem eventually_band_smoothed_pivot : ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ critical b : ℝ, ∀ h : List ℝ,
    BandSourceData κ B cap μ critical u h → 0 < b →
    smoothedBandWeight u (u/bandRatio) (Real.log b) ≠ 0 →
    b ≤ B ∧ bandPad u < cappedStep μ B b ∧
      Real.log (cappedStep μ B b-bandPad u) ∈ Icc (innerBandLow u) (innerBandHigh u) := by
  filter_upwards [eventually_band_smoothing_endpoints,eventually_band_smoothing_separated,
    eventually_inner_band_kernel_window,eventually_inner_band_geometry,eventually_outer_band_log_window]
    with u hEnds hSeparated hWindow hGeometry hOuter
  intro κ B cap μ critical b h S hb hWeight
  let lo := innerBandLow u
  let hi := innerBandHigh u
  let ALo := bandCutoff μ u lo
  let AHi := bandCutoff μ u hi
  let P := bandPad u
  let φ := cappedStep μ B
  have hRootU := hSeparated.1
  have hRootV := band_lower_scale_positive hRootU
  have hSupport := smoothedBandWeight_support hRootU hRootV hSeparated.2 hWeight
  have hEnd := hEnds B μ S.threshold_gt_one S.scale_upper S.mu_positive S.curvature_half
  have hLoOuter := (hWindow lo 0 ⟨le_rfl,hGeometry.2.2.1⟩ (by omega)).1
  have hHiOuter := (hWindow hi 0 ⟨hGeometry.2.2.1,le_rfl⟩ (by omega)).1
  have Wlo := hOuter B μ lo S.threshold_gt_one S.scale_upper S.mu_positive S.curvature_half hLoOuter
  have Whi := hOuter B μ hi S.threshold_gt_one S.scale_upper S.mu_positive S.curvature_half hHiOuter
  have hALo : 0 < ALo := Wlo.2.2.1
  have hAHi : 0 < AHi := Whi.2.2.1
  have hLoLog : Real.log ALo < Real.log b := hEnd.1.trans_lt hSupport.1
  have hHiLog : Real.log b < Real.log AHi := hSupport.2.trans_le hEnd.2
  have hLb : ALo < b := (Real.log_lt_log_iff hALo hb).mp hLoLog
  have hUb : b < AHi := (Real.log_lt_log_iff hb hAHi).mp hHiLog
  have hη := firstAverageEta_bounds.1
  have hAB : AHi ≤ B := Whi.2.2.2.2.2.2.2.2.1.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le S.threshold_gt_one.le
      (show 1-firstAverageEta ≤ (1:ℝ) by linarith only [hη]))
  have hφ := cappedStep_strictMono (B:=B) S.mu_positive (by linarith only [S.curvature_half])
  have hLoφ := hφ hLb
  have hHiφ := hφ hUb
  have hLoBranch : φ ALo = P+Real.exp lo := Wlo.2.2.2.2.2.2.2.2.2.2
  have hHiBranch : φ AHi = P+Real.exp hi := Whi.2.2.2.2.2.2.2.2.2.2
  change φ ALo < φ b at hLoφ
  change φ b < φ AHi at hHiφ
  rw [hLoBranch] at hLoφ
  rw [hHiBranch] at hHiφ
  have hActive : P < φ b := (lt_add_of_pos_right P (Real.exp_pos lo)).trans hLoφ
  have hLow : lo ≤ Real.log (φ b-P) := (Real.le_log_iff_exp_le (sub_pos.mpr hActive)).mpr (by linarith only [hLoφ])
  have hHigh : Real.log (φ b-P) ≤ hi := (Real.log_le_iff_le_exp (sub_pos.mpr hActive)).mpr (by linarith only [hHiφ])
  exact ⟨hUb.le.trans hAB,hActive,hLow,hHigh⟩

end
end StrongSilver
