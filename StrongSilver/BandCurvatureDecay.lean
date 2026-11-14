-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandLocalScaleBounds

namespace StrongSilver
open Real Filter Set
noncomputable section
set_option maxHeartbeats 5000000

def bandCurvatureExponent : ℝ := bandPowerGap firstAverageEta/2

theorem bandCurvatureExponent_positive : 0 < bandCurvatureExponent := by
  have hη := firstAverageEta_bounds.1
  have hDen : 0 < 1-firstAverageEta := sub_pos.mpr (firstAverageEta_bounds.2.trans (by norm_num))
  unfold bandCurvatureExponent bandPowerGap
  positivity

theorem power_gap_curvature {A B μ q : ℝ} (hA : 0 < A) (hμ : 0 ≤ μ)
    (hGap : A^(1+q) ≤ B) (hμB : μ*B ≤ 1/2) : μ*A ≤ (1/2:ℝ)*A^(-q) := by
  have hh := (mul_le_mul_of_nonneg_left hGap hμ).trans hμB
  have hScale := mul_le_mul_of_nonneg_right hh (Real.rpow_pos_of_pos hA (-q)).le
  have hCancel : A^q*A^(-q) = 1 := by rw [← Real.rpow_add hA,add_neg_cancel,Real.rpow_zero]
  have hEq : (μ*A^(1+q))*A^(-q) = μ*A := by
    rw [Real.rpow_add hA,Real.rpow_one]
    calc
      _ = μ*A*(A^q*A^(-q)) := by ring
      _ = _ := by rw [hCancel,mul_one]
  rwa [hEq] at hScale

/-- The local cutoff is a fixed power below the original cap, so its
curvature product decays exponentially in the band scale. -/
theorem eventually_band_curvature_decay : ∀ᶠ u : ℝ in atTop,
    ∀ B μ y : ℝ, 1 < B → u ≤ firstAverageLogScale B → 0 < μ → μ*B ≤ 1/2 →
    y ∈ Icc (outerBandLow u) (outerBandHigh u) →
    μ*bandCutoff μ u y ≤ (1/2:ℝ)*Real.exp (-bandCurvatureExponent*u) := by
  filter_upwards [eventually_outer_band_log_window] with u H
  intro B μ y hB hU hμ hμB hy
  let A := bandCutoff μ u y
  have W := H B μ y hB hU hμ hμB hy
  have hA : 0 < A := W.2.2.1
  have hη := firstAverageEta_bounds.1
  have hη1 : firstAverageEta < 1 := firstAverageEta_bounds.2.trans (by norm_num)
  have hGap := band_cutoff_power_gap hη hη1 hA (zero_lt_one.trans hB) W.2.2.2.2.2.2.2.2.1
  have hLow : u/2 ≤ Real.log A := W.2.2.2.2.2.2.2.2.2.1
  have hq : 0 < bandPowerGap firstAverageEta := by unfold bandPowerGap; positivity
  have hPow := power_gap_curvature hA hμ.le hGap hμB
  have hExp : A^(-bandPowerGap firstAverageEta) ≤ Real.exp (-bandCurvatureExponent*u) := by
    rw [Real.rpow_def_of_pos hA]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonpos_right hLow (neg_nonpos.mpr hq.le)
    unfold bandCurvatureExponent
    nlinarith only [hh]
  exact hPow.trans (mul_le_mul_of_nonneg_left hExp (by norm_num : (0:ℝ) ≤ 1/2))

end
end StrongSilver
