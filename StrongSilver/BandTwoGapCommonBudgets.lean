-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandLocalScaleBounds
import StrongSilver.TwoGapBudgetAsymptotics

namespace StrongSilver
open Real Filter Set
noncomputable section
set_option maxHeartbeats 5400000

/-- The concrete L,U,N chosen from the actual inverse band cutoff
satisfy every common signed-mass and suffix-error budget of the finite
two-gap construction. -/
theorem eventually_band_two_gap_common_budgets {c : ℝ} (hc : 0 < c) : ∀ᶠ u : ℝ in atTop,
    ∀ B μ y : ℝ, 1 < B → u ≤ firstAverageLogScale B → 0 < μ → μ*B ≤ 1/2 →
    y ∈ Icc (outerBandLow u) (outerBandHigh u) →
    let A := bandCutoff μ u y
    let L := bandLocalLowerScale u A
    let U := bandLocalUpperScale u A
    let N := bandLocalNegativeScale u A
    1000 ≤ L ∧ N ≤ L/1000 ∧ 2*U*N ≤ c*L^2 ∧ 2*U*A^(-(1:ℝ)/20) ≤ c*L := by
  obtain ⟨A₀,hSource⟩ := eventually_atTop.mp (eventually_two_gap_common_budgets
    (K:=bandLocalCommonConstant) (γ:=(1:ℝ)/100) bandLocalCommonConstant_positive hc (by norm_num))
  filter_upwards [eventually_band_local_scale_bounds,eventually_outer_band_log_window,eventually_band_cutoff_ge A₀,
    eventually_ge_atTop (2:ℝ)] with u hLocal hWindow hMinimum hu
  intro B μ y hB hU hμ hμB hy
  let A := bandCutoff μ u y
  have W := hWindow B μ y hB hU hμ hμB hy
  have hA : 0 < A := W.2.2.1
  have hLogLower : u/2 ≤ Real.log A := W.2.2.2.2.2.2.2.2.2.1
  have hLogUpper : Real.log A ≤ (1001:ℝ)/1000*u := W.2.2.2.2.1
  have hu0 : 0 < u := lt_of_lt_of_le (by norm_num) hu
  have hLog : 1 ≤ Real.log A := by linarith only [hu,hLogLower]
  have hComparison1 : u ≤ 2*Real.log A := by linarith only [hLogLower]
  have hComparison2 : Real.log A ≤ 2*u := by linarith only [hLogUpper,hu0]
  have hBounds := hLocal A hA hLog hComparison1 hComparison2
  have hUp : 0 ≤ bandLocalUpperScale u A := by unfold bandLocalUpperScale; positivity
  have hNp : 0 ≤ bandLocalNegativeScale u A := by unfold bandLocalNegativeScale; positivity
  exact hSource A (hMinimum B μ y hB hU hμ hμB hy)
    (bandLocalLowerScale u A) (bandLocalUpperScale u A) (bandLocalNegativeScale u A)
    hUp hNp hBounds.1 hBounds.2.1 hBounds.2.2

end
end StrongSilver
