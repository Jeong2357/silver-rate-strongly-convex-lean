-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandSmoothedPivotGeometry
import StrongSilver.KernelSmoothingMargins
import StrongSilver.BandGoodChildGeometry

namespace StrongSilver
open ScheduleTree BinaryForest Real Filter Set
noncomputable section
set_option maxHeartbeats 8000000

def bandHeightWeight (μ u y : ℝ) : ℝ :=
  smoothedBandWeight u (u/bandRatio) (Real.log (bandCutoff μ u y))

theorem continuous_smoothedBandWeight (u v : ℝ) : Continuous (smoothedBandWeight u v) := by
  unfold smoothedBandWeight thresholdRamp
  fun_prop

theorem bandHeightWeight_continuous {μ u : ℝ} (hμ : 0 < μ) : Continuous (bandHeightWeight μ u) := by
  have hP : 0 ≤ bandPad u := (Real.exp_pos _).le
  have hd : Differentiable ℝ (fun y => Real.log (logarithmicCutoff μ (bandPad u) y)) := by
    intro y
    exact ((logarithmicCutoff_hasDerivAt hμ y).log (logarithmicCutoff_positive hμ hP).ne').differentiableAt
  exact (continuous_smoothedBandWeight u (u/bandRatio)).comp hd.continuous

theorem eventually_band_height_weight_bounds : ∀ᶠ u : ℝ in atTop, ∀ μ y : ℝ,
    0 ≤ bandHeightWeight μ u y ∧ bandHeightWeight μ u y ≤ 1 := by
  filter_upwards [eventually_band_smoothing_separated] with u hSeparated
  intro μ y
  exact smoothedBandWeight_bounds hSeparated.1 (band_lower_scale_positive hSeparated.1) hSeparated.2

/-- Every protected actual pivot is recovered by the same inverse
cutoff branch used to transport the smoothed averaging weight. -/
theorem eventually_band_protected_cutoff_inverse : ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ critical : ℝ, ∀ h : List ℝ, ∀ q : ScheduleNode,
    BandSourceData κ B cap μ critical u h → bandProtectedPredicate B μ u q →
    bandCutoff μ u (nodePaddedHeight (cappedStep μ B) (bandPad u) q) = q.pivot := by
  filter_upwards [eventually_eligible_band_step_upper] with u hUpper
  intro κ B cap μ critical h q S hq
  have hCap := hUpper B μ q.pivot q.pivotIndex S.threshold_gt_one S.scale_upper S.mu_positive S.curvature_half
    (bandProtectedPredicate_eligible hq)
  have hSmall : μ*q.pivot < 1 := (mul_le_mul_of_nonneg_left hCap S.mu_positive.le).trans_lt (by linarith only [S.curvature_half])
  have hRoot : bandPad u < logarithmicStep μ q.pivot := by simpa only [cappedStep,if_pos hCap] using hq.1
  have hh := logarithmicCutoff_inverts (P:=bandPad u) S.mu_positive hSmall hRoot
  dsimp only [ScheduleNode.pivot] at hCap hh
  simpa only [bandCutoff,nodePaddedHeight,nodeHeight,ScheduleNode.pivot,cappedStep,if_pos hCap] using hh

/-- The smoothing weight changes by at most its logarithmic
Lipschitz constant times the actual height displacement. -/
theorem eventually_band_kernel_weight_difference : ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ critical y : ℝ, ∀ h : List ℝ, ∀ q : ScheduleNode,
    BandSourceData κ B cap μ critical u h → bandProtectedPredicate B μ u q →
    |smoothedBandWeight u (u/bandRatio) (Real.log q.pivot)-bandHeightWeight μ u y| ≤
      (3/Real.sqrt u)*|y-nodePaddedHeight (cappedStep μ B) (bandPad u) q| := by
  filter_upwards [eventually_band_protected_cutoff_inverse,eventually_gt_atTop (0:ℝ)] with u hInverse hu
  intro κ B cap μ critical y h q S hq
  let z := nodePaddedHeight (cappedStep μ B) (bandPad u) q
  have hI := hInverse κ B cap μ critical h q S hq
  have hLip := band_weight_lipschitz hu (Real.log (bandCutoff μ u y)) (Real.log (bandCutoff μ u z))
  have hDist := logCutoff_lipschitz (P:=bandPad u) S.mu_positive (Real.exp_pos _).le z y
  have hFactor : 0 ≤ 3/Real.sqrt u := div_nonneg (by norm_num) (Real.sqrt_nonneg u)
  change |Real.log (bandCutoff μ u y)-Real.log (bandCutoff μ u z)| ≤ _ at hDist
  change bandCutoff μ u z = q.pivot at hI
  rw [hI] at hLip hDist
  have hDistScale := mul_le_mul_of_nonneg_left hDist hFactor
  unfold bandHeightWeight
  rw [abs_sub_comm]
  exact hLip.trans hDistScale

/-- If a protected pivot has nonzero original threshold weight,
its entire kernel interval lies in the fixed inner integration band. -/
theorem eventually_band_weighted_kernel_support : ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ critical : ℝ, ∀ h : List ℝ, ∀ q : ScheduleNode,
    BandSourceData κ B cap μ critical u h → bandProtectedPredicate B μ u q →
    smoothedBandWeight u (u/bandRatio) (Real.log q.pivot) ≠ 0 →
    innerBandLow u ≤ nodePaddedHeight (cappedStep μ B) (bandPad u) q ∧
    nodePaddedHeight (cappedStep μ B) (bandPad u) q+((fourPhaseDepth u+2:ℕ):ℝ)*Real.log rho ≤ innerBandHigh u := by
  filter_upwards [eventually_band_protected_cutoff_inverse,eventually_band_cutoff_log_distance,
    eventually_band_smoothing_separated,eventually_kernel_support_margin] with u hInverse hDistance hSeparated hMargin
  intro κ B cap μ critical h q S hq hWeight
  let z := nodePaddedHeight (cappedStep μ B) (bandPad u) q
  have hI := hInverse κ B cap μ critical h q S hq
  have hOuter : z ∈ Icc (outerBandLow u) (outerBandHigh u) :=
    ⟨hq.2.1.le,by have hh := hq.2.2; dsimp only [z]; linarith only [hh,visibilitySpacing_positive]⟩
  have hD := hDistance B μ z S.threshold_gt_one S.scale_upper S.mu_positive S.curvature_half hOuter
  change bandCutoff μ u z = q.pivot at hI
  rw [hI] at hD
  have hSupport := smoothedBandWeight_support hSeparated.1 (band_lower_scale_positive hSeparated.1) hSeparated.2 hWeight
  have hDlo := (abs_le.mp hD).1
  have hDhi := (abs_le.mp hD).2
  have hω := log_rho_positive
  have hSpan : 0 ≤ ((fourPhaseDepth u:ℝ)+2)*Real.log rho := by positivity
  dsimp only [innerBandLow,innerBandHigh,z]
  push_cast
  constructor <;> linarith only [hDlo,hDhi,hSupport.1,hSupport.2,hMargin,hSpan]

end
end StrongSilver
