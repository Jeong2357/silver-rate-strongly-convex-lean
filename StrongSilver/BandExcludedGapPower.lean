-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ExcludedGapPowerBound
import StrongSilver.BandLogWindow
import StrongSilver.BandEligibleSteps
import StrongSilver.TreeRootOrder

namespace StrongSilver
open ScheduleTree BinaryForest Real Filter Set
noncomputable section
set_option maxHeartbeats 4200000

/-- The excluded-gap power estimate at every actual band cutoff. Every
refinement pivot is eligible by the concrete band-height bounds; there
is no assumed logarithmic-saving or forest-count inequality. -/
theorem eventually_band_excluded_gap_power : ∀ᶠ u : ℝ in atTop,
    ∀ B μ κ y : ℝ, ∀ start k : ℕ, ∀ t : ScheduleTree,
    1 < B → u ≤ firstAverageLogScale B → 0 < μ → μ*B ≤ 1/2 → 0 ≤ κ →
    y ∈ Icc (outerBandLow u) (outerBandHigh u) →
    y-(k:ℝ)*Real.log rho ∈ Icc (outerBandLow u) (outerBandHigh u) →
    k ≤ fourPhaseDepth u+2 → t.Cartesian → cappedStep μ B t.rootStep ≤ bandPad u+Real.exp y →
    ((labels (indexedHeightWindow (cappedStep μ B) (bandPad u) (y-(k:ℝ)*Real.log rho) start κ t)).map
      (normalizedNodeDecrease (cappedStep μ B) (bandPad u))).sum ≤
      splitCoefficient*gapSavingsMaximum (cappedStep μ B) (bandPad u) κ (2400/u) start t.word (bandEligible μ B u)+
        (76800*splitCoefficient)*(2:ℝ)^fourPhaseDepth u/u := by
  filter_upwards [eventually_excluded_gap_power_bound,eventually_outer_band_log_window] with u hBound hWindow
  intro B μ κ y start k t hB hU hμ hμB hκ hy hlow hk ht hupper
  let low := y-(k:ℝ)*Real.log rho
  let A := bandCutoff μ u low
  have W := hWindow B μ low hB hU hμ hμB hlow
  have hA : 0 < A := W.2.2.1
  have hcut : cappedStep μ B A = bandPad u+Real.exp low := W.2.2.2.2.2.2.2.2.2.2
  have hφ := cappedStep_strictMono hμ (by linarith only [hμB] : μ*B < 1)
  apply hBound (cappedStep μ B) (bandPad u) κ y A start k t (bandEligible μ B u)
    hφ (Real.exp_pos _) hκ (by simp only [cappedStep,if_pos (zero_lt_one.trans hB).le,logarithmicStep_zero,le_refl])
    hA.le hcut hk ht hupper
  intro j b hb hAb
  have hφb := hφ hAb
  rw [hcut] at hφb
  have hpositive : bandPad u < cappedStep μ B b := by have he := Real.exp_pos low; linarith only [hφb,he]
  have hheight : low < Real.log (cappedStep μ B b-bandPad u) :=
    (Real.lt_log_iff_exp_lt (sub_pos.mpr hpositive)).mpr (by linarith only [hφb])
  have hbUpper := (hφ.monotone (cartesian_word_le_root ht hb)).trans hupper
  have hheightUpper := Real.log_le_log (sub_pos.mpr hpositive)
    (show cappedStep μ B b-bandPad u ≤ Real.exp y by linarith only [hbUpper])
  rw [Real.log_exp] at hheightUpper
  exact decide_eq_true ⟨hpositive,hlow.1.trans hheight.le,hheightUpper.trans hy.2⟩

end
end StrongSilver
