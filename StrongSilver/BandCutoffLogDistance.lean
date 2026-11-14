-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.LogCutoffOrder
import StrongSilver.BandPadRatio

namespace StrongSilver
open Real Filter Set
noncomputable section
set_option maxHeartbeats 5200000

/-- Throughout the enlarged source band, logarithmic cutoff and
transformed height differ by at most log 2. -/
theorem eventually_band_cutoff_log_distance : ∀ᶠ u : ℝ in atTop,
    ∀ B μ y : ℝ, 1 < B → u ≤ firstAverageLogScale B → 0 < μ → μ*B ≤ 1/2 →
    y ∈ Icc (outerBandLow u) (outerBandHigh u) →
    |Real.log (bandCutoff μ u y)-y| ≤ Real.log 2 := by
  filter_upwards [eventually_outer_band_log_window,eventually_band_pad_small] with u hWindow hPad
  intro B μ y hB hU hμ hμB hy
  let P := bandPad u
  let A := bandCutoff μ u y
  have W := hWindow B μ y hB hU hμ hμB hy
  have hA : 0 < A := W.2.2.1
  have hP : 0 < P := Real.exp_pos _
  have hPad0 : P ≤ Real.exp y := by
    have hh := (hPad.2 y hy.1).1
    linarith only [hh,Real.exp_pos y]
  have hSize := logarithmicCutoff_size hμ hP.le W.2.1
  have hLower : Real.exp y/2 ≤ A := by dsimp only [A,bandCutoff]; linarith only [hSize.1,hP]
  have hUpper : A ≤ 2*Real.exp y := by dsimp only [A,bandCutoff]; linarith only [hSize.2.1,hPad0]
  have hLogUpper : Real.log A ≤ y+Real.log 2 := by
    apply (Real.log_le_iff_le_exp hA).mpr
    rw [Real.exp_add,Real.exp_log (by norm_num : (0:ℝ) < 2)]
    linear_combination hUpper
  have hLogLower : y-Real.log 2 ≤ Real.log A := by
    apply (Real.le_log_iff_exp_le hA).mpr
    rw [Real.exp_sub,Real.exp_log (by norm_num : (0:ℝ) < 2)]
    exact hLower
  exact abs_le.mpr ⟨by linarith only [hLogLower],by linarith only [hLogUpper]⟩

end
end StrongSilver
