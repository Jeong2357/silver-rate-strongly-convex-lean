-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.RootCandidateIntegrability

namespace StrongSilver
open ScheduleTree BinaryForest Real Filter Set MeasureTheory
noncomputable section
set_option maxHeartbeats 6400000

/-- Step 1 of (4.25): all actual gaps outside S(y), with gamma=1/100,
are controlled by the root/parent, following-bad, and following-rank
budgets derived from the original stable signed schedule. -/
theorem eventually_band_root_candidate_budget : ∃ C > 0, ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ critical a b : ℝ, ∀ h : List ℝ,
    1 < κ → 1 < B → B ≤ cap → cap ≤ κ → B ≤ κ/128 → u ≤ firstAverageLogScale B →
    1/κ ≤ μ → μ ≤ 2/κ → μ*B ≤ 1/2 → a ≤ b → outerBandLow u < a →
    b+Real.log u/200+3*visibilitySpacing ≤ outerBandHigh u →
    (∀ z ∈ h, 1-μ*z ≠ 0) → inverseChargeAbove (κ/4) h μ ≤ critical →
    critical ≤ 34*weightedCount h cap*cap^(-nu) → D κ h ≤ 1 →
    1 ≤ countAbove h B → κ^nu ≤ weightedCount h cap →
    (∫ y in a..b, rootCandidateExclusionObservable κ B μ u (Real.log u/200) h y) ≤
      C*weightedCount h cap*(u^((9:ℝ)/10)+u^(1-nu/200)) := by
  obtain ⟨Cr,hCr,Hr⟩ := eventually_band_bad_root_parent
  obtain ⟨Cf,hCf,Hf⟩ := eventually_band_following_bad
  refine ⟨Cr+Cf+4,by positivity,?_⟩
  filter_upwards [Hr,Hf,eventually_band_large_following_integral,eventually_band_candidate_exclusions_pointwise,
    eventually_ge_atTop (1:ℝ)] with u hRoot hFollow hLarge hPoint hu
  intro κ B cap μ critical a b h hκ hB hBcap hcapκ hBκ hU hμ hμu hμB hab ha hb hcrit hcritical hcriticalRank hD hcount hκW
  have hμ0 := (one_div_pos.mpr (zero_lt_one.trans hκ)).trans_le hμ
  have hφ := cappedStep_monotone (B:=B) hμ0 (by linarith only [hμB])
  have hWidth : 0 ≤ Real.log u/200 := div_nonneg (Real.log_nonneg hu) (by norm_num)
  have hb' : b+3*visibilitySpacing ≤ outerBandHigh u := by linarith only [hb,hWidth]
  have hbL : b+Real.log u/200 ≤ outerBandHigh u := by linarith only [hb,visibilitySpacing_positive]
  have hR := hRoot κ B cap μ critical a b h hκ hB hBcap hcapκ hBκ hU hμ hμu hμB hab ha hb' hcrit hcritical hcriticalRank hD hcount hκW
  have hF := hFollow κ B cap μ critical a b h hκ hB hBcap hcapκ hU hμ hμu hμB hab hcrit hcritical hcriticalRank hD hcount hκW
  have hL := hLarge κ B cap μ a b h hB hBcap hU hμ0 hμB hab ha.le hbL
  have hIntR := badRootParentObservable_integrable κ B μ u a b h
  have hIntF := linkedFollowingObservable_integrable (cappedStep μ B) hφ (bandPad u) κ nu a b (bandBadIndicator B μ u) h
  have hIntL := largeFollowingObservable_integrable (cappedStep μ B) hφ (bandPad u) κ nu (Real.log u/200) a b hWidth h
  have hI := intervalIntegral.integral_mono_on hab
    (rootCandidateExclusionObservable_integrable κ B μ u (Real.log u/200) a b h)
    ((hIntR.add hIntF).add hIntL) (by
      intro y hy
      apply hPoint κ B μ y (Real.log u/200) h (zero_lt_one.trans hκ) hB hBκ hU hμ0 hμB (ha.trans_le hy.1)
      linarith only [hy.2,hb])
  rw [intervalIntegral.integral_add (hIntR.add hIntF) hIntL,intervalIntegral.integral_add hIntR hIntF] at hI
  have hPower := Real.rpow_le_rpow_of_exponent_le hu (by norm_num : (1:ℝ)/5 ≤ 9/10)
  have hRate := mul_le_mul_of_nonneg_left hPower (mul_nonneg hCf.le (weightedCount_nonneg h cap))
  have hW := weightedCount_nonneg h cap
  have hPow1 := (Real.rpow_pos_of_pos (zero_lt_one.trans_le hu) ((9:ℝ)/10)).le
  have hPow2 := (Real.rpow_pos_of_pos (zero_lt_one.trans_le hu) (1-nu/200)).le
  have hCross1 : 0 ≤ 4*weightedCount h cap*u^((9:ℝ)/10) := by positivity
  have hCross2 : 0 ≤ (Cr+Cf)*weightedCount h cap*u^(1-nu/200) := by positivity
  linear_combination hI+hR+hF+hL+hRate+hCross1+hCross2

end
end StrongSilver
