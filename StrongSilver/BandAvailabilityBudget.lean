-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandReservedPairCount
import StrongSilver.BandPreAvailabilityBudget

namespace StrongSilver
open ScheduleTree BinaryForest Real Filter Set MeasureTheory
noncomputable section
set_option maxHeartbeats 6400000

theorem bandAvailabilityEnvelope_integrable (κ B cap μ u width a b : ℝ) (n : ℕ) (h : List ℝ) :
    IntervalIntegrable (bandAvailabilityEnvelope κ B cap μ u width n h) volume a b :=
  (preAvailableExclusionObservable_integrable κ B μ u width a b n h).add intervalIntegrable_const

/-- The complete pair-availability envelope in (4.25), including the
actual full-cut reservation. It dominates each admissible reserved
pair deficit pointwise, so no measurability of a selected reservation
function is assumed. -/
theorem eventually_band_availability_budget : ∃ C > 0, ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ critical a b : ℝ, ∀ h : List ℝ,
    1 < κ → 1 < B → B ≤ cap → cap ≤ κ → B ≤ κ/128 → u ≤ firstAverageLogScale B →
    1/κ ≤ μ → μ ≤ 2/κ → μ*B ≤ 1/2 → a ≤ b → outerBandLow u < a →
    b+Real.log u/200+3*visibilitySpacing ≤ outerBandHigh u →
    (∀ z ∈ h, 1-μ*z ≠ 0) → inverseChargeAbove (κ/4) h μ ≤ critical →
    critical ≤ 34*weightedCount h cap*cap^(-nu) → D κ h ≤ 1 →
    1 ≤ countAbove h B → κ^nu ≤ weightedCount h cap →
    (∫ y in a..b, bandAvailabilityEnvelope κ B cap μ u (Real.log u/200) (fourPhaseDepth u+1) h y) ≤
      C*weightedCount h cap*(u^((9:ℝ)/10)*(2:ℝ)^fourPhaseDepth u+u^(1-nu/200)) := by
  obtain ⟨C,hC,H⟩ := eventually_band_pre_availability_budget
  refine ⟨C+64,by positivity,?_⟩
  filter_upwards [H,eventually_band_bin_geometry,
    eventually_sqrt_affine_le_linear (by norm_num : (0:ℝ) < 1) 4 0,eventually_ge_atTop (1:ℝ)]
    with u hPre hGeometry hSqrt hu
  intro κ B cap μ critical a b h hκ hB hBcap hcapκ hBκ hU hμ hμu hμB hab ha hb hcrit hcritical hcriticalRank hD hcount hκW
  have hBase := hPre κ B cap μ critical a b h hκ hB hBcap hcapκ hBκ hU hμ hμu hμB hab ha hb hcrit hcritical hcriticalRank hD hcount hκW
  have hu0 := zero_lt_one.trans_le hu
  have hW := weightedCount_nonneg h cap
  have hWidth : 0 ≤ Real.log u/200 := div_nonneg (Real.log_nonneg hu) (by norm_num)
  have hHigh : outerBandHigh u ≤ 2*u := by unfold outerBandHigh; linarith only [hSqrt]
  have hLow : 0 ≤ outerBandLow u := (by norm_num : (0:ℝ) ≤ 1).trans hGeometry.1
  have hLen : b-a ≤ 2*u := by linarith only [ha,hb,hHigh,hLow,hWidth,visibilitySpacing_positive]
  have hCoeff : 0 ≤ 32*weightedCount h cap/u := by positivity
  have hLength := mul_le_mul_of_nonneg_right hLen hCoeff
  have hCancel : (2*u)*(32*weightedCount h cap/u) = 64*weightedCount h cap := by field_simp [hu0.ne']; ring
  rw [hCancel] at hLength
  have hConst : (∫ _y in a..b, (32*weightedCount h cap/u)) ≤ 64*weightedCount h cap := by
    simpa only [intervalIntegral.integral_const,smul_eq_mul] using hLength
  have hA : (1:ℝ) ≤ u^((9:ℝ)/10) := Real.one_le_rpow hu (by norm_num)
  have hTwo : (1:ℝ) ≤ (2:ℝ)^fourPhaseDepth u := one_le_pow₀ (by norm_num)
  have hPositive : 0 ≤ u^(1-nu/200) := (Real.rpow_pos_of_pos hu0 _).le
  have hFactor : (1:ℝ) ≤ u^((9:ℝ)/10)*(2:ℝ)^fourPhaseDepth u+u^(1-nu/200) := by
    nlinarith only [hA,hTwo,hPositive,mul_nonneg (sub_nonneg.mpr hA) (sub_nonneg.mpr hTwo)]
  have hRate := mul_le_mul_of_nonneg_left hFactor (show 0 ≤ 64*weightedCount h cap by positivity)
  unfold bandAvailabilityEnvelope
  rw [intervalIntegral.integral_add
    (preAvailableExclusionObservable_integrable κ B μ u (Real.log u/200) a b (fourPhaseDepth u+1) h) intervalIntegrable_const]
  linear_combination hBase+hConst+hRate

end
end StrongSilver
