-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FullWorkingCutLoss
import StrongSilver.BandPointwiseBounds

namespace StrongSilver
open Real Filter Set
noncomputable section
set_option maxHeartbeats 5500000

/-- Weighted source-cut prices, including the exact logarithmic
transform conversion, are uniformly O(W/u) on the band. -/
theorem eventually_band_working_cut_loss : ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ critical : ℝ, ∀ h : List ℝ,
    1 < κ → 1 < B → B ≤ cap → cap ≤ κ → u ≤ firstAverageLogScale B →
    1/κ ≤ μ → μ ≤ 2/κ → μ*B ≤ 1/2 →
    (∀ z ∈ h, 1-μ*z ≠ 0) → inverseChargeAbove (κ/4) h μ ≤ critical →
    critical ≤ 34*weightedCount h cap*cap^(-nu) → D κ h ≤ 1 →
    ∀ y ∈ Icc (outerBandLow u) (outerBandHigh u),
    Real.exp (nu*y)*(workingCutLoss (bandCutoff μ u y) κ μ
      ((bandCutoff μ u y)^(1+bandUpsilon firstAverageEta)) (bandPad u)
      (bandSigma firstAverageEta) (bandTau firstAverageEta) (bandFullCut μ u y h)/2+
        4*μ*clippedMass h B) ≤ 4804*weightedCount h cap/u := by
  have hη := firstAverageEta_bounds.1
  have hη1 : firstAverageEta < 1 := firstAverageEta_bounds.2.trans (by norm_num)
  obtain ⟨hσ,hσmax,hτ,hτmax,hσυ,hτυ,hυmax,hυq⟩ := band_exponent_bounds hη firstAverageEta_small
  obtain ⟨A₀,hSource⟩ := eventually_atTop.mp
    (eventually_full_working_cut_loss hσ hσmax hτ hτmax hσυ hτυ hυmax hυq)
  filter_upwards [eventually_outer_band_log_window,eventually_band_cutoff_ge A₀,eventually_gt_atTop (0:ℝ)]
    with u hWindow hMinimum hu
  intro κ B cap μ critical h hκ hB hBcap hcapκ hU hμ hμu hμB hcrit hcritical hcriticalRank hD y hy
  let A := bandCutoff μ u y
  have hμ0 := (one_div_pos.mpr (zero_lt_one.trans hκ)).trans_le hμ
  have W := hWindow B μ y hB hU hμ0 hμB hy
  have hA : 0 < A := W.2.2.1
  have hLow : u/2 ≤ Real.log A := W.2.2.2.2.2.2.2.2.2.1
  have hLog : 0 < Real.log A := (by linarith only [hu] : 0 < u/2).trans_le hLow
  have hGap := band_cutoff_power_gap hη hη1 hA (zero_lt_one.trans hB) W.2.2.2.2.2.2.2.2.1
  have H := hSource A (hMinimum B μ y hB hU hμ0 hμB hy) κ B cap μ (bandPad u) critical h
    hκ hGap hBcap hcapκ hμ hμu hμB W.2.2.2.2.2.1 W.2.2.2.2.2.2.1 W.2.2.2.2.2.2.2.1
    hcrit hcritical hcriticalRank hD
  have hP : 0 < bandPad u := Real.exp_pos _
  have hSize := logarithmicCutoff_size hμ0 hP.le W.2.1
  have hHeight : Real.exp y ≤ 2*A := by dsimp only [A,bandCutoff]; linarith only [hSize.1,hP]
  have hNorm := height_power_normalization hA hHeight
  have hWeighted := mul_le_mul_of_nonneg_left H (Real.exp_pos (nu*y)).le
  have hNormScale := mul_le_mul_of_nonneg_left hNorm
    (show 0 ≤ 1201*weightedCount h cap/Real.log A by have hw := weightedCount_nonneg h cap; positivity)
  have hInv : 1/Real.log A ≤ 2/u := (div_le_div_iff₀ hLog hu).mpr (by linarith only [hLow])
  have hInvScale := mul_le_mul_of_nonneg_left hInv
    (show 0 ≤ 2402*weightedCount h cap by have hw := weightedCount_nonneg h cap; positivity)
  dsimp only [A,bandFullCut] at hWeighted hNormScale hInvScale ⊢
  linear_combination hWeighted+hNormScale+hInvScale

end
end StrongSilver
