-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandFullKernelBudget

namespace StrongSilver
open ScheduleTree BinaryForest Real Filter Set MeasureTheory
noncomputable section
set_option maxHeartbeats 7000000

/-- Normalize a finite silver kernel budget using its exact positive
mass, without imposing a sign on the signed source integral. -/
theorem normalize_silver_kernel_upper {I K W E : ℝ} (hK : 0 ≤ K) (hW : 0 ≤ W) (hE : 0 ≤ E) (d : ℕ)
    (hI : I ≤ K*W*(1+(2:ℝ)^d*E)) :
    I/silverKernelMass d ≤ K*nu*W*(1/(2:ℝ)^d+E) := by
  have hN : 0 < (2:ℝ)^d := pow_pos (by norm_num) d
  have hMass := silverKernelMass_positive d
  have hBound : 0 ≤ K*W*(1+(2:ℝ)^d*E) := by positivity
  calc
    _ ≤ (K*W*(1+(2:ℝ)^d*E))/silverKernelMass d := div_le_div_of_nonneg_right hI hMass.le
    _ ≤ (K*W*(1+(2:ℝ)^d*E))/((2:ℝ)^d/nu) :=
      div_le_div_of_nonneg_left hBound (div_pos hN nu_positive) (silverKernelMass_bounds d).1
    _ = _ := by field_simp [hN.ne',nu_positive.ne'] <;> ring

/-- The full source kernel has the normalized order required by the
band power estimate: inverse-cubic log plus a fixed negative power. -/
theorem eventually_band_normalized_kernel_budget {C : ℝ} (hC : 0 < C) : ∃ K > 0, ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ critical a b : ℝ, ∀ h : List ℝ,
    BandSourceData κ B cap μ critical u h → a ≤ b → innerBandLow u ≤ a → b ≤ innerBandHigh u →
    (∫ y in a..b, bandFullKernelEnvelope C κ B cap μ u h y)/silverKernelMass (fourPhaseDepth u) ≤
      K*weightedCount h cap*(1/(Real.log u)^3+u^(-(1:ℝ)/1000)) := by
  obtain ⟨K0,hK0,HB⟩ := eventually_band_full_kernel_budget hC
  refine ⟨4*K0*nu,by have hν := nu_positive; positivity,?_⟩
  filter_upwards [HB,eventually_band_kernel_error_rate,Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)),
    eventually_gt_atTop (0:ℝ)] with u hBudget hError hLog hu
  intro κ B cap μ critical a b h S hab ha hb
  have hW := weightedCount_nonneg h cap
  have hν := nu_positive
  have hE : 0 ≤ bandKernelError u := by
    have hδ : 0 ≤ bandTolerance u := (Real.rpow_pos_of_pos hu _).le
    unfold bandKernelError
    positivity
  have hI := hBudget κ B cap μ critical a b h S hab ha hb
  have hNorm := normalize_silver_kernel_upper hK0.le hW hE (fourPhaseDepth u) hI
  have hCoeff : 0 ≤ K0*nu*weightedCount h cap := by have hν := nu_positive; positivity
  have hErrorScale := mul_le_mul_of_nonneg_left hError hCoeff
  have hInv := fourPhaseDepth_inverse_group_bound hLog
  have hInverseScale := mul_le_mul_of_nonneg_left hInv (show 0 ≤ 4*K0*nu*weightedCount h cap by positivity)
  have hPositive : 0 ≤ (K0*nu*weightedCount h cap)/(2:ℝ)^fourPhaseDepth u := by positivity
  linear_combination hNorm+hErrorScale+hInverseScale+3*hPositive

end
end StrongSilver
