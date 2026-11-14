-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandCurvatureDecay

namespace StrongSilver
open Real Filter Set
noncomputable section
set_option maxHeartbeats 5400000

/-- Original signed negative mass is negligible relative to the next
candidate gap's actual positive root step. -/
theorem eventually_band_negative_scale_small : ∀ᶠ u : ℝ in atTop,
    ∀ A b : ℝ, 0 ≤ A → bandRootScaleConstant*A ≤ b → bandLocalNegativeScale u A ≤ b/16 := by
  filter_upwards [eventually_const_mul_log_pow_mul_power_le 0 (128:ℝ)
    (by norm_num : -(19:ℝ)/200 < 0) bandRootScaleConstant_positive] with u H
  simp only [pow_zero,mul_one] at H
  intro A b hA hb
  have hh := mul_le_mul_of_nonneg_right H hA
  unfold bandLocalNegativeScale
  linear_combination (1/16:ℝ)*hh+(1/16:ℝ)*hb

/-- The actual signed prefix-mass curvature term tends uniformly to
zero throughout the inverse band window. -/
theorem eventually_band_curvature_mass_small {ε : ℝ} (hε : 0 < ε) : ∀ᶠ u : ℝ in atTop,
    ∀ B μ y M : ℝ, 1 < B → u ≤ firstAverageLogScale B → 0 < μ → μ*B ≤ 1/2 →
    y ∈ Icc (outerBandLow u) (outerBandHigh u) → M ≤ 36*bandCutoff μ u y → μ*M ≤ ε := by
  filter_upwards [eventually_band_curvature_decay,eventually_exp_negative_linear_le_inverse bandCurvatureExponent_positive,
    eventually_ge_atTop (18/ε),eventually_ge_atTop (1:ℝ)] with u hRate hExp huε hu
  intro B μ y M hB hU hμ hμB hy hM
  have hu0 := zero_lt_one.trans_le hu
  have hR := hRate B μ y hB hU hμ hμB hy
  have hMass := mul_le_mul_of_nonneg_left hM hμ.le
  have hInv : 18/u ≤ ε := by
    apply (div_le_iff₀ hu0).mpr
    have hh := (div_le_iff₀ hε).mp huε
    nlinarith only [hh]
  linear_combination hMass+36*hR+18*hExp+hInv

/-- The exact tolerance plus actual prefix-mass curvature satisfies
the smallness radius of the finite two-gap trajectory. -/
theorem eventually_band_two_gap_near {τ : ℝ} (hτ : 0 < τ) : ∀ᶠ u : ℝ in atTop,
    ∀ B μ y M : ℝ, 1 < B → u ≤ firstAverageLogScale B → 0 < μ → μ*B ≤ 1/2 →
    y ∈ Icc (outerBandLow u) (outerBandHigh u) → M ≤ 36*bandCutoff μ u y →
    4*bandTolerance u+μ*M ≤ τ := by
  have ht := tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/10)
  filter_upwards [eventually_band_curvature_mass_small (show 0 < τ/2 by positivity),
    ht.eventually (gt_mem_nhds (show (0:ℝ) < τ/8 by positivity))] with u hMass hTol
  intro B μ y M hB hU hμ hμB hy hM
  have hh := hMass B μ y M hB hU hμ hμB hy hM
  have hδ : bandTolerance u ≤ τ/8 := by simpa only [bandTolerance,neg_div] using hTol.le
  linarith only [hh,hδ]

end
end StrongSilver
