-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FrontierPositiveMass
import StrongSilver.BandPadRatio
import StrongSilver.HeightMassNormalization
import StrongSilver.BandExcludedForest

namespace StrongSilver
open ScheduleTree Scalar.SignedIntervals Real Filter Set
noncomputable section
set_option maxHeartbeats 4200000

/-- Uniform positive transformed mass of all actual frontier gaps. This
is the mass budget for low-root child intervals in the availability count. -/
theorem eventually_band_frontier_mass_budget : ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ y : ℝ, ∀ h : List ℝ,
    1 < B → B ≤ cap → u ≤ firstAverageLogScale B → 0 < μ → μ*B ≤ 1/2 →
    y ∈ Icc (outerBandLow u) (outerBandHigh u) →
    Real.exp ((nu-1)*y)*((bandIndexedFrontier κ B μ u y h).map fun q => positiveMass (q.source.word.map (cappedStep μ B))).sum ≤
      (4/(1-nu))*weightedCount h cap := by
  filter_upwards [eventually_outer_band_log_window,eventually_band_pad_small] with u hWindow hPad
  intro κ B cap μ y h hB hBcap hU hμ hμB hy
  let A := bandCutoff μ u y
  have W := hWindow B μ y hB hU hμ hμB hy
  have hA : 0 < A := W.2.2.1
  have hη := firstAverageEta_bounds.1
  have hBpower : B^(1-firstAverageEta) ≤ B := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hB.le
      (show 1-firstAverageEta ≤ (1:ℝ) by linarith only [hη])
  have hAB : A ≤ B := W.2.2.2.2.2.2.2.2.1.trans hBpower
  have hφ := cappedStep_strictMono hμ (by linarith only [hμB] : μ*B < 1)
  have hbranch : cappedStep μ B A = bandPad u+Real.exp y := W.2.2.2.2.2.2.2.2.2.2
  have hcut := heightCut_eq_fullCut hφ hbranch (cartesian h).word
  have hzero : cappedStep μ B 0 ≤ bandPad u+Real.exp y := by
    rw [cappedStep,if_pos (zero_lt_one.trans hB).le,logarithmicStep_zero]
    exact add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  have hsum := indexedFrontier_positive_mass (κ := κ) (cappedStep μ B) hφ.monotone hzero (cartesian h) (cartesian_valid h)
  rw [hcut,cartesian_word] at hsum
  have hMass := fullCut_capped_positive_mass hμ hA hAB hBcap hμB h
  have hsize := logarithmicCutoff_size hμ (show (0:ℝ) ≤ bandPad u by exact (Real.exp_pos _).le) W.2.1
  have hpad := (hPad.2 y hy.1).1
  have hA2 : A ≤ 2*Real.exp y := by
    have hsizeUpper : A ≤ bandPad u+Real.exp y := hsize.2.1
    linarith only [hsizeUpper,hpad,Real.exp_pos y]
  have hNormalize := height_positive_mass_normalization hA hA2
  have hMass' := mul_le_mul_of_nonneg_left hMass (Real.exp_pos ((nu-1)*y)).le
  have hden : 0 < 1-nu := by linarith only [nu_lt_one]
  have hCoeff : 0 ≤ 2*weightedCount h cap/(1-nu) := div_nonneg (mul_nonneg (by norm_num) (weightedCount_nonneg h cap)) hden.le
  have h2 := mul_le_mul_of_nonneg_left hNormalize hCoeff
  change Real.exp ((nu-1)*y)*((indexedFrontier (cappedStep μ B) (bandPad u+Real.exp y) 0 κ (cartesian h)).map _).sum ≤ _
  rw [hsum]
  linear_combination hMass'+h2

end
end StrongSilver
