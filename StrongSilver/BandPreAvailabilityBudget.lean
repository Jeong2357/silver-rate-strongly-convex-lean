-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PreAvailablePairCount
import StrongSilver.BandExponentialIntegral

namespace StrongSilver
open ScheduleTree BinaryForest Real Filter Set MeasureTheory
noncomputable section
set_option maxHeartbeats 6800000

/-- Pair availability before the actual finite reservation. The
reservation contributes a further O(W) integrated count, supplied
pointwise by BandPairReservation. -/
theorem eventually_band_pre_availability_budget : ∃ C > 0, ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ critical a b : ℝ, ∀ h : List ℝ,
    1 < κ → 1 < B → B ≤ cap → cap ≤ κ → B ≤ κ/128 → u ≤ firstAverageLogScale B →
    1/κ ≤ μ → μ ≤ 2/κ → μ*B ≤ 1/2 → a ≤ b → outerBandLow u < a →
    b+Real.log u/200+3*visibilitySpacing ≤ outerBandHigh u →
    (∀ z ∈ h, 1-μ*z ≠ 0) → inverseChargeAbove (κ/4) h μ ≤ critical →
    critical ≤ 34*weightedCount h cap*cap^(-nu) → D κ h ≤ 1 →
    1 ≤ countAbove h B → κ^nu ≤ weightedCount h cap →
    (∫ y in a..b, preAvailableExclusionObservable κ B μ u (Real.log u/200) (fourPhaseDepth u+1) h y) ≤
      C*weightedCount h cap*(u^((9:ℝ)/10)*(2:ℝ)^fourPhaseDepth u+u^(1-nu/200)) := by
  obtain ⟨Ct,hCt,Ht⟩ := eventually_band_root_candidate_budget
  obtain ⟨Cd,hCd,Hd⟩ := eventually_band_candidate_depth_failures
  let Ce := 4/nu
  have hCe : 0 < Ce := div_pos (by norm_num) nu_positive
  refine ⟨Ce+2*Ct+Cd,by positivity,?_⟩
  filter_upwards [Ht,Hd,eventually_band_exponential_integral,eventually_ge_atTop (1:ℝ)] with u hRoot hDepth hExp hu
  intro κ B cap μ critical a b h hκ hB hBcap hcapκ hBκ hU hμ hμu hμB hab ha hb hcrit hcritical hcriticalRank hD hcount hκW
  have hμ0 := (one_div_pos.mpr (zero_lt_one.trans hκ)).trans_le hμ
  have hWidth : 0 ≤ Real.log u/200 := div_nonneg (Real.log_nonneg hu) (by norm_num)
  have hTop : b ∈ Icc (outerBandLow u) (outerBandHigh u) := by
    constructor
    · exact ha.le.trans hab
    · linarith only [hb,hWidth,visibilitySpacing_positive]
  have hR := hRoot κ B cap μ critical a b h hκ hB hBcap hcapκ hBκ hU hμ hμu hμB hab ha hb hcrit hcritical hcriticalRank hD hcount hκW
  have hD' := hDepth κ B cap μ critical a b (Real.log u/200) h hκ hB hBcap hcapκ hBκ hU hμ hμu hμB hab hcrit hcritical hcriticalRank hD hcount hκW
  have hE := hExp B cap μ a b h hB hBcap hU hμ0 hμB hab hTop hcount
  have hIntE : IntervalIntegrable (fun y : ℝ => Real.exp (nu*y)) volume a b :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable a b
  have hIntR := rootCandidateExclusionObservable_integrable κ B μ u (Real.log u/200) a b h
  have hIntD := candidateDepthFailureObservable_integrable κ B μ u (Real.log u/200) a b (fourPhaseDepth u+1) h
  have hI := intervalIntegral.integral_mono_on hab
    (preAvailableExclusionObservable_integrable κ B μ u (Real.log u/200) a b (fourPhaseDepth u+1) h)
    ((hIntE.add (hIntR.const_mul 2)).add hIntD)
    (fun y _ => preAvailable_exclusion_pointwise κ B μ u (Real.log u/200) (fourPhaseDepth u+1) h y)
  rw [intervalIntegral.integral_add (hIntE.add (hIntR.const_mul 2)) hIntD,
    intervalIntegral.integral_add hIntE (hIntR.const_mul 2),intervalIntegral.integral_const_mul] at hI
  have hPow : (1:ℝ) ≤ u^((9:ℝ)/10) := Real.one_le_rpow hu (by norm_num)
  have hTwo : (1:ℝ) ≤ (2:ℝ)^fourPhaseDepth u := one_le_pow₀ (by norm_num)
  have hFactor : (1:ℝ) ≤ u^((9:ℝ)/10)*(2:ℝ)^fourPhaseDepth u := by
    nlinarith only [hPow,hTwo,mul_nonneg (sub_nonneg.mpr hPow) (sub_nonneg.mpr hTwo)]
  have hA : u^((9:ℝ)/10) ≤ u^((9:ℝ)/10)*(2:ℝ)^fourPhaseDepth u := by
    have hh := mul_le_mul_of_nonneg_left hTwo (by positivity : 0 ≤ u^((9:ℝ)/10))
    simpa only [mul_one] using hh
  have hW := weightedCount_nonneg h cap
  have hRateE := mul_le_mul_of_nonneg_left hFactor (mul_nonneg hCe.le hW)
  have hRateR := mul_le_mul_of_nonneg_left hA (show 0 ≤ 2*Ct*weightedCount h cap by positivity)
  have hCross : 0 ≤ (Ce+Cd)*weightedCount h cap*u^(1-nu/200) := by positivity
  change _ ≤ Ce*weightedCount h cap at hE
  linear_combination hI+hE+2*hR+hD'+hRateE+hRateR+hCross

end
end StrongSilver
