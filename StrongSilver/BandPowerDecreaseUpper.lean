-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandWeightedJumpSupport
import StrongSilver.BandEnvelopeNonnegative
import StrongSilver.BandNormalizedKernelBudget

namespace StrongSilver
open ScheduleTree BinaryForest Real Filter Set MeasureTheory
noncomputable section
set_option maxHeartbeats 10000000

/-- The actual averaged power decrease has the uniform summable band
upper bound. All analytic estimates are derived from the source data. -/
theorem eventually_band_power_decrease_upper : ∃ K > 0, ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ critical : ℝ, ∀ h : List ℝ,
    BandSourceData κ B cap μ critical u h →
    averagedPowerDecrease (cappedStep μ B) κ h u (u/bandRatio) ≤
      K*weightedCount h cap*(1/(Real.log u)^3+u^(-(1:ℝ)/1000)) := by
  obtain ⟨C,hC,Hfull⟩ := eventually_band_full_kernel_envelope
  obtain ⟨Kb,hKb,Hbudget⟩ := eventually_band_normalized_kernel_budget hC
  obtain ⟨Ka,hKa,Happrox⟩ := eventually_band_kernel_approximation
  refine ⟨Kb+Ka+2,by positivity,?_⟩
  filter_upwards [Hfull,Hbudget,Happrox,eventually_band_gamma_to_jumps,eventually_band_kernel_representation,
    eventually_band_height_weight_bounds,eventually_inner_band_geometry,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))]
    with u hFull hBudget hApprox hGamma hRep hWeight hGeometry hLog
  intro κ B cap μ critical h S
  have hPoint : ∀ y ∈ Icc (innerBandLow u) (innerBandHigh u),
      bandKernelConvolution κ B μ u h y ≤ bandFullKernelEnvelope C κ B cap μ u h y := by
    intro y hy
    have hRaw := hFull κ B cap μ critical y h S hy
    have hIdentity := hRep κ B μ y h S.mu_positive S.curvature_half hy
    have hχ := hWeight μ y
    have hEnv := bandFullKernelEnvelope_nonnegative hC hGeometry.1 κ B cap μ y h
    have hFirst := mul_le_mul_of_nonneg_left hRaw hχ.1
    have hSecond := mul_le_mul_of_nonneg_right hχ.2 hEnv
    have hEq : bandKernelConvolution κ B μ u h y =
        bandHeightWeight μ u y*(Real.exp (nu*y)*((bandIndexedFrontier κ B μ u y h).map
          (bandKernelGapPower B μ u y)).sum) := by
      unfold bandKernelConvolution
      rw [hIdentity]
      ring
    rw [hEq]
    exact hFirst.trans (by simpa only [one_mul] using hSecond)
  have hIntegral := intervalIntegral.integral_mono_on hGeometry.2.2.1
    (bandKernelConvolution_integral (κ:=κ) (B:=B) (u:=u) h S.mu_positive).1
    (bandFullKernelEnvelope_integrable (C:=C) (κ:=κ) (cap:=cap) (u:=u) h S.threshold_gt_one S.mu_positive S.curvature_half) hPoint
  have hNormalized := div_le_div_of_nonneg_right hIntegral (silverKernelMass_positive (fourPhaseDepth u)).le
  have hUpper := hBudget κ B cap μ critical (innerBandLow u) (innerBandHigh u) h S hGeometry.2.2.1 le_rfl le_rfl
  have hError := (abs_le.mp (hApprox κ B cap μ critical h S)).2
  have hSource := hGamma κ B cap μ critical h S
  have hW := weightedCount_nonneg h cap
  have hInverse : 0 ≤ 1/(Real.log u)^3 := by positivity
  have hExtra : 0 ≤ (Ka+2)*weightedCount h cap*(1/(Real.log u)^3) := by positivity
  linear_combination hSource+hError+hNormalized+hUpper+hExtra

end
end StrongSilver
