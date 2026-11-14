-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandCutObservables

namespace StrongSilver
open Real Filter Set
noncomputable section
set_option maxHeartbeats 4800000

/-- All pointwise cut budgets hold uniformly on the enlarged band for
the actual stable signed schedule. No log-product or refinement bound
is retained as an analytic assumption. -/
theorem eventually_band_pointwise_bounds : ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ critical : ℝ, ∀ h : List ℝ,
    1 < κ → 1 < B → B ≤ cap → cap ≤ κ → u ≤ firstAverageLogScale B →
    1/κ ≤ μ → μ ≤ 2/κ → μ*B ≤ 1/2 →
    (∀ b ∈ h, 1-μ*b ≠ 0) → inverseChargeAbove (κ/4) h μ ≤ critical →
    critical ≤ 34*weightedCount h cap*cap^(-nu) → D κ h ≤ 1 →
    1 ≤ countAbove h B → κ^nu ≤ weightedCount h cap →
    ∀ y ∈ Icc (outerBandLow u) (outerBandHigh u), BandCutBounds κ B cap μ u y h := by
  have hη := firstAverageEta_bounds.1
  have hη1 : firstAverageEta < 1 := firstAverageEta_bounds.2.trans (by norm_num)
  obtain ⟨hσ,hσmax,hτ,hτmax,hσυ,hτυ,hυmax,hυq⟩ := band_exponent_bounds hη firstAverageEta_small
  have hlog := eventually_full_working_log_lower hσ hσmax hτ hτmax hσυ hτυ hυmax hυq
  have href := eventually_full_cut_refinement_savings hσ hσmax hτ hτmax hσυ hτυ hυmax hυq
  obtain ⟨A₀,hall⟩ := eventually_atTop.mp (hlog.and href)
  filter_upwards [eventually_outer_band_log_window,eventually_eligible_band_step,
    eventually_band_cutoff_ge A₀,eventually_gt_atTop (0:ℝ)] with u hwindow heligible hminimum hu
  intro κ B cap μ critical h hκ hB hBcap hcapκ hU hμ hμu hμB hcrit hcritical hcriticalRank hD hcountB hκW y hy
  let P := bandPad u
  let A := bandCutoff μ u y
  have hP : 0 < P := Real.exp_pos _
  have hW := weightedCount_nonneg h cap
  have hκ0 := zero_lt_one.trans hκ
  have hμ0 := (one_div_pos.mpr hκ0).trans_le hμ
  have W := hwindow B μ y hB hU hμ0 hμB hy
  have hA : 0 < A := W.2.2.1
  have hAupper : A ≤ B^(1-firstAverageEta) := W.2.2.2.2.2.2.2.2.1
  have hhalf : u/2 ≤ Real.log A := W.2.2.2.2.2.2.2.2.2.1
  have hlogA : 0 < Real.log A := (by linarith only [hu] : 0 < u/2).trans_le hhalf
  have hAhi : Real.log A ≤ (1001:ℝ)/1000*u := W.2.2.2.2.1
  have hPL : A^((49:ℝ)/50) ≤ P := W.2.2.2.2.2.1
  have hPU : P ≤ A^((199:ℝ)/200) := W.2.2.2.2.2.2.1
  have hPA : 2*P ≤ A := W.2.2.2.2.2.2.2.1
  have hAB : A ≤ B := hAupper.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hB.le
      (show 1-firstAverageEta ≤ (1:ℝ) by linarith only [hη]))
  have hAcap := hAB.trans hBcap
  have hAκ := hAcap.trans hcapκ
  have hgap := band_cutoff_power_gap hη hη1 hA (zero_lt_one.trans hB) hAupper
  have hAge : A₀ ≤ A := hminimum B μ y hB hU hμ0 hμB hy
  have hsource := hall A hAge
  have hlow := hsource.1 κ B cap μ P critical h hκ hgap hBcap hcapκ hμ hμu hμB hPL hPU hPA hcrit hcritical hcriticalRank hD
  have hprice : 1200/Real.log A ≤ 2400/u := by
    have hh := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1200) (by positivity : 0 < u/2) hhalf
    have he : 1200/(u/2) = 2400/u := by ring
    rwa [he] at hh
  have helig : ∀ j b, bandEligible μ B u j b = true → A^((499:ℝ)/500) ≤ b ∧ 2*P ≤ b := by
    intro j b hb
    have H := heligible B μ b j hB hU hμ0 hμB hb
    exact ⟨band_selected_lower hA H.1 hu.le H.2.1 hAhi,H.2.2.2⟩
  have hsave := hsource.2 κ B cap μ P critical (2400/u) h (bandEligible μ B u)
    hκ hgap hBcap hcapκ hμ hμu hμB hPL hPU hPA hprice helig hcrit hcritical hcriticalRank hD
  have hsmall : μ*(P+Real.exp y) ≤ 1/2 := W.2.1
  have hsize := logarithmicCutoff_size hμ0 hP.le hsmall
  have hsizeLow : (P+Real.exp y)/2 ≤ A := hsize.1
  have hheight : Real.exp y ≤ 2*A := by nlinarith only [hsizeLow,hP]
  have hnorm := height_rank_error_normalization hA hu (weightedCount_nonneg h cap) (by norm_num : (0:ℝ) ≤ 1201) hheight hhalf
  have hlowMul := mul_le_mul_of_nonneg_left hlow (Real.exp_pos (nu*y)).le
  have hsaveMul := mul_le_mul_of_nonneg_left hsave (Real.exp_pos (nu*y)).le
  have hcount : 1 ≤ countAbove h A := hcountB.trans (countAbove_antitone h hAB)
  have hLS := full_cut_positive_sum_log_rank_upper hμ0 hA (zero_lt_one.trans hB) hAB hAcap hμB hP
    (by linarith only [hPA]) hAκ h hcount
  have hPS := full_cut_positive_sum_power_rank_upper hμ0 hA (zero_lt_one.trans hB) hAB hAcap hμB hP
    (by linarith only [hPA,hP]) hκ0.le h hcount
  have hLorder := cutLogProduct_le_positivePart (cappedStep μ B) hP hκ0.le (fullCut A h) (by
    intro q hq
    have hq0 := hA.trans (fullCut_pivot hq)
    exact (hq0.trans_le (cappedStep_ge hμ0 (by linarith only [hμB]) q.pivot)).le)
  have hLSmul := mul_le_mul_of_nonneg_left hLS (Real.exp_pos (nu*y)).le
  have hcancel := height_power_normalization hA hheight
  have hden : 0 < 1-nu := by linarith only [nu_lt_one]
  have hClog : 0 ≤ (4/(1-nu)+4)*weightedCount h cap := by positivity
  have hnormLS := mul_le_mul_of_nonneg_left hcancel hClog
  refine {
    signed_log_lower := ?_
    positive_log_upper := ?_
    log_order := ?_
    power_order := hPS.1
    positive_power_upper := ?_
    savings_nonnegative := totalGapSavingsMaximum_nonnegative _ _ _ _ _ _
    savings_upper := ?_
  }
  · change -4804*weightedCount h cap/u ≤ Real.exp (nu*y)*(cutLogProduct (cappedStep μ B) P κ (fullCut A h)-Real.log κ)
    linear_combination hlowMul+hnorm
  · unfold bandLogUpperConstant
    change Real.exp (nu*y)*(cutLogProduct (positivePartStep (cappedStep μ B)) P κ (fullCut A h)-Real.log κ) ≤ _
    linear_combination hLSmul+hnormLS
  · exact sub_le_sub_right hLorder (Real.log κ)
  · unfold bandPowerUpperConstant
    change cutPower (positivePartStep (cappedStep μ B)) P κ (fullCut A h) ≤ _
    linear_combination hPS.2+hκW
  · change Real.exp (nu*y)*totalGapSavingsMaximum (cappedStep μ B) P κ (2400/u) (bandEligible μ B u) (fullCut A h) ≤
      Real.exp (nu*y)*(cutLogProduct (cappedStep μ B) P κ (fullCut A h)-Real.log κ)+4804*weightedCount h cap/u
    linear_combination hsaveMul+hnorm

end
end StrongSilver
