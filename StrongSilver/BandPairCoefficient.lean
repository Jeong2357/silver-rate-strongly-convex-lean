-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandPairGroupError

namespace StrongSilver
open Real Filter Set
noncomputable section
set_option maxHeartbeats 4600000

/-- The actual endpoint coefficient is controlled by the same band
tolerance as the source good-vertex estimates. -/
theorem eventually_band_pair_coefficient : ∀ᶠ u : ℝ in atTop,
    ∀ B μ y M : ℝ, 1 < B → u ≤ firstAverageLogScale B → 0 < μ → μ*B ≤ 1/2 →
    y ∈ Icc (outerBandLow u) (outerBandHigh u) → M ≤ 36*bandCutoff μ u y →
    4*bandTolerance u+μ*M ≤ 6*bandTolerance u := by
  have hη := firstAverageEta_bounds.1
  have hη1 : firstAverageEta < 1 := firstAverageEta_bounds.2.trans (by norm_num)
  have hq : 0 < bandPowerGap firstAverageEta := by unfold bandPowerGap; positivity
  obtain ⟨A₀,hSmall⟩ := eventually_atTop.mp (eventually_curvature_below_balance (K:=36) hq)
  filter_upwards [eventually_outer_band_log_window,eventually_band_cutoff_ge A₀,eventually_ge_atTop (1:ℝ)]
    with u hWindow hMinimum hu
  intro B μ y M hB hU hμ hμB hy hM
  let A := bandCutoff μ u y
  have W := hWindow B μ y hB hU hμ hμB hy
  have hA : 0 < A := W.2.2.1
  have hLow : u ≤ 2*Real.log A := by
    have hh : u/2 ≤ Real.log A := W.2.2.2.2.2.2.2.2.2.1
    linarith only [hh]
  have hHigh : Real.log A ≤ 2*u := by
    have hh : Real.log A ≤ (1001:ℝ)/1000*u := W.2.2.2.2.1
    linarith only [hh,hu]
  have hu0 := zero_lt_one.trans_le hu
  have hLog : 0 < Real.log A := by linarith only [hLow,hu0]
  have hGap := band_cutoff_power_gap hη hη1 hA (zero_lt_one.trans hB) W.2.2.2.2.2.2.2.2.1
  have hCurv := power_gap_curvature hA hμ.le hGap hμB
  have hMass := mul_le_mul_of_nonneg_left hM hμ.le
  have hPowPos := Real.rpow_pos_of_pos hA (-bandPowerGap firstAverageEta)
  have hError := hSmall A (hMinimum B μ y hB hU hμ hμB hy)
  have hComparable := comparable_rpow_upper hLog hu0 hHigh hLow
    (by norm_num : -(1:ℝ) ≤ -(1:ℝ)/10) (by norm_num : -(1:ℝ)/10 ≤ 1)
  change (Real.log A)^(-(1:ℝ)/10) ≤ 2*bandTolerance u at hComparable
  dsimp only [A] at hCurv hMass hPowPos hError hComparable ⊢
  linear_combination hMass+36*hCurv+hError+hComparable+18*hPowPos.le

end
end StrongSilver
