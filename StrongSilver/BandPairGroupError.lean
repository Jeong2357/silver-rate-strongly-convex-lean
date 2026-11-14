-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.TwoGapGroupCountError
import StrongSilver.BandCurvatureDecay
import StrongSilver.PowerMargins

namespace StrongSilver
open Real Filter Set
noncomputable section
set_option maxHeartbeats 6500000

/-- The actual depth is chosen from u, rather than log A. The uniform
cutoff comparison still gives the required group-count bound. -/
theorem eventually_band_group_count_log_cutoff : ∀ᶠ u : ℝ in atTop,
    ∀ A : ℝ, 0 < A → u ≤ 2*Real.log A → Real.log A ≤ 2*u →
    (2:ℝ)^fourPhaseDepth u ≤ (Real.log A)^((1:ℝ)/1000) := by
  obtain ⟨x₀,hPower⟩ := eventually_atTop.mp
    (eventually_const_mul_power_le (by norm_num : (1:ℝ)/2000 < 1/1000) 2)
  filter_upwards [eventually_fourPhaseGroupCount_le_power (by norm_num : (0:ℝ) < 1/2000),
    eventually_ge_atTop (2*x₀),eventually_ge_atTop (1:ℝ)] with u hCount hu₀ hu
  intro A hA hLower hUpper
  have hu0 := zero_lt_one.trans_le hu
  have hLog : 0 < Real.log A := by linarith only [hLower,hu0]
  have hComparison := comparable_rpow_upper hu0 hLog hLower hUpper
    (by norm_num : -(1:ℝ) ≤ 1/2000) (by norm_num : (1:ℝ)/2000 ≤ 1)
  exact hCount.trans (hComparison.trans (hPower (Real.log A) (by linarith only [hu₀,hLower])))

/-- The actual group-count error in a band is at most 2/u, uniformly
in the original source schedule and the inverse cutoff. -/
theorem eventually_band_pair_group_error : ∀ᶠ u : ℝ in atTop,
    ∀ B μ y M : ℝ, 1 < B → u ≤ firstAverageLogScale B → 0 < μ → μ*B ≤ 1/2 →
    y ∈ Icc (outerBandLow u) (outerBandHigh u) → 0 ≤ M → M ≤ 36*bandCutoff μ u y →
    let A := bandCutoff μ u y
    (2:ℝ)^fourPhaseDepth u*(μ*M+μ*bandLocalUpperScale u A+workingGateFraction A+
      2*bandLocalUpperScale u A*A^(-(1:ℝ)/20)/bandLocalLowerScale u A) ≤ 2/u := by
  let K := max bandLocalCommonConstant 36
  have hK : 0 < K := bandLocalCommonConstant_positive.trans_le (le_max_left _ _)
  have hη := firstAverageEta_bounds.1
  have hη1 : firstAverageEta < 1 := firstAverageEta_bounds.2.trans (by norm_num)
  have hq : 0 < bandPowerGap firstAverageEta := by unfold bandPowerGap; positivity
  obtain ⟨A₀,hError⟩ := eventually_atTop.mp
    (eventually_two_gap_group_error_by_count (K:=K) (γ:=(1:ℝ)/100) hK hq)
  filter_upwards [eventually_band_group_count_log_cutoff,eventually_band_local_scale_bounds,
    eventually_outer_band_log_window,eventually_band_cutoff_ge A₀,eventually_ge_atTop (2:ℝ)]
    with u hCount hLocal hWindow hMinimum hu
  intro B μ y M hB hU hμ hμB hy hM hMbound
  let A := bandCutoff μ u y
  have W := hWindow B μ y hB hU hμ hμB hy
  have hA : 0 < A := W.2.2.1
  have hLow : u ≤ 2*Real.log A := by
    have hh : u/2 ≤ Real.log A := W.2.2.2.2.2.2.2.2.2.1
    linarith only [hh]
  have hHigh : Real.log A ≤ 2*u := by
    have hh : Real.log A ≤ (1001:ℝ)/1000*u := W.2.2.2.2.1
    linarith only [hh,hu]
  have hLog : 1 ≤ Real.log A := by linarith only [hu,hLow]
  have hL := hLocal A hA hLog hLow hHigh
  have hs := Real.rpow_pos_of_pos (zero_lt_one.trans_le hLog) ((1:ℝ)/1000)
  have hDen := mul_le_mul_of_nonneg_right (le_max_left bandLocalCommonConstant (36:ℝ)) hs.le
  have hLlower : A/(K*(Real.log A)^((1:ℝ)/1000)) ≤ bandLocalLowerScale u A :=
    (div_le_div_of_nonneg_left hA.le (mul_pos bandLocalCommonConstant_positive hs) hDen).trans hL.1
  have hMupper : M ≤ K*A := hMbound.trans
    (mul_le_mul_of_nonneg_right (le_max_right bandLocalCommonConstant (36:ℝ)) hA.le)
  have hUupper : bandLocalUpperScale u A ≤ K*A*(Real.log A)^((1:ℝ)/100) := hL.2.1.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left bandLocalCommonConstant (36:ℝ)) hA.le)
      (Real.rpow_pos_of_pos (zero_lt_one.trans_le hLog) ((1:ℝ)/100)).le)
  have hGap := band_cutoff_power_gap hη hη1 hA (zero_lt_one.trans hB) W.2.2.2.2.2.2.2.2.1
  have hCurv := power_gap_curvature hA hμ.le hGap hμB
  have hCurv' : μ*A ≤ A^(-bandPowerGap firstAverageEta) := by
    have hh := Real.rpow_pos_of_pos hA (-bandPowerGap firstAverageEta)
    linarith only [hCurv,hh]
  have hU0 : 0 ≤ bandLocalUpperScale u A := by unfold bandLocalUpperScale; positivity
  have hResult := hError A (hMinimum B μ y hB hU hμ hμB hy) μ M (bandLocalUpperScale u A)
    (bandLocalLowerScale u A) ((2:ℝ)^fourPhaseDepth u) (hCount A hA hLow hHigh)
    hμ.le hM hU0 hLlower hMupper hUupper hCurv'
  have hInverse : 1/Real.log A ≤ 2/u := by
    apply (div_le_div_iff₀ (by linarith only [hLog] : 0 < Real.log A) (by linarith only [hu] : 0 < u)).mpr
    linarith only [hLow]
  exact hResult.trans hInverse

end
end StrongSilver
