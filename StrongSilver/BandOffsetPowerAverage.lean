-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandPadErrorRate
import StrongSilver.SmoothedBandGeometry
import StrongSilver.BandSourceData
import StrongSilver.OriginalLogPowerAverage

namespace StrongSilver
open ScheduleTree Real Filter Set MeasureTheory
noncomputable section
set_option maxHeartbeats 9500000

/-- Increasing the common pad is bounded by one original gap count;
this estimate applies with the same terminal reserve. -/
theorem cutPower_pad_upper (φ : ℝ → ℝ) {P κ : ℝ} (hP : 0 ≤ P) (hκ : 0 ≤ κ) (C : ScheduleCut) :
    cutPower φ P κ C ≤ cutPower φ 1 κ C+((C.phases.length:ℝ)+1)*P^nu := by
  have hMono := cutPower_pad_mono φ hP (show P ≤ 1+P by linarith) hκ C
  have hIncrement := cutPower_pad_increment φ (by norm_num : (0:ℝ) ≤ 1) hP hκ C
  exact hMono.trans hIncrement

/-- The exact offset-P original jump sum bounds Gamma up to the
summably small source rank cost of changing the common pad. -/
theorem eventually_band_offset_power_average : ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ critical : ℝ, ∀ h : List ℝ,
    BandSourceData κ B cap μ critical u h →
    averagedPowerDecrease (cappedStep μ B) κ h u (u/bandRatio) ≤
      (((cartesian h).reservedNodes κ).map fun q => smoothedBandWeight u (u/bandRatio) (Real.log q.1.rootStep)*
        paddedRootDecrease (cappedStep μ B) (bandPad u) q.2 q.1).sum+2*weightedCount h cap*u^(-(1:ℝ)/1000) := by
  filter_upwards [eventually_band_smoothing_separated,eventually_band_pad_rank_error,eventually_ge_atTop (1:ℝ)]
    with u hSeparated hPadError hu
  intro κ B cap μ critical h S
  let φ := cappedStep μ B
  let P := bandPad u
  let v := u/bandRatio
  let W := weightedCount h cap
  let ε := 2*W*(P^nu*Real.exp (-nu*v))
  have hκ : 0 ≤ κ := (zero_lt_one.trans S.kappa_gt_one).le
  have hW : 0 ≤ W := weightedCount_nonneg h cap
  have hP : 0 ≤ P := (Real.exp_pos _).le
  have hP1 : 1 ≤ P := Real.one_le_exp_iff.mpr (by positivity)
  have hv : 0 < v := band_lower_scale_positive hSeparated.1
  have huB : u ≤ Real.log B := by
    have hh := S.scale_upper
    have hη := firstAverageEta_bounds.1
    have hLogB := Real.log_pos S.threshold_gt_one
    dsimp only [firstAverageLogScale] at hh
    nlinarith only [hh,hη,hLogB]
  have hPoint : ∀ t ∈ Icc (0:ℝ) 1,
      cutPower φ 1 κ (fullCut (Real.exp (u+t*Real.sqrt u)) h)-cutPower φ 1 κ (fullCut (Real.exp (v+t*Real.sqrt v)) h) ≤
      cutPower φ P κ (fullCut (Real.exp (u+t*Real.sqrt u)) h)-cutPower φ P κ (fullCut (Real.exp (v+t*Real.sqrt v)) h)+ε := by
    intro t ht
    let A := Real.exp (v+t*Real.sqrt v)
    have hA : 0 < A := Real.exp_pos _
    have hLow : Real.exp v ≤ A := Real.exp_le_exp.mpr (le_add_of_nonneg_right (mul_nonneg ht.1 (Real.sqrt_nonneg _)))
    have hTime : v+t*Real.sqrt v ≤ u := by
      have hh := mul_le_mul_of_nonneg_right ht.2 (Real.sqrt_nonneg v)
      have hSep : v+Real.sqrt v ≤ u := hSeparated.2
      linarith only [hh,hSep]
    have hAB : A ≤ B := by
      exact (Real.exp_le_exp.mpr (hTime.trans huB)).trans_eq (Real.exp_log (zero_lt_one.trans S.threshold_gt_one))
    have hCount : 1 ≤ countAbove h A := S.threshold_count.trans (countAbove_antitone h hAB)
    have hRank := full_cut_gap_count_rank hA (hAB.trans S.threshold_le_cap) h hCount
    have hInv := Real.rpow_le_rpow_of_nonpos (Real.exp_pos v) hLow (neg_nonpos.mpr nu_positive.le)
    have hExp : (Real.exp v)^(-nu) = Real.exp (-nu*v) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos v),Real.log_exp]
      congr 1
      ring
    rw [hExp] at hInv
    have hRankScale := mul_le_mul_of_nonneg_left hInv (show 0 ≤ 2*W by positivity)
    have hGap : (((fullCut A h).phases.length:ℝ)+1) ≤ 2*W*Real.exp (-nu*v) := hRank.trans hRankScale
    have hGapScale := mul_le_mul_of_nonneg_right hGap (Real.rpow_pos_of_pos (Real.exp_pos ((987:ℝ)/1000*u)) nu).le
    have hUpper := cutPower_pad_mono φ (by norm_num : (0:ℝ) ≤ 1) hP1 hκ (fullCut (Real.exp (u+t*Real.sqrt u)) h)
    have hLower := cutPower_pad_upper φ hP hκ (fullCut A h)
    dsimp only [A,ε,P,W,bandPad] at hUpper hLower hGapScale ⊢
    linear_combination hUpper+hLower+hGapScale
  have hInt (Q w : ℝ) : IntervalIntegrable (fun t : ℝ => cutPower φ Q κ (fullCut (Real.exp (w+t*Real.sqrt w)) h)) volume 0 1 :=
    cutObservable_intervalIntegrable (cutPower φ Q κ) 0 h _ (by fun_prop) 0 1
  have hGamma1 := (hInt 1 u).sub (hInt 1 v)
  have hGammaP := (hInt P u).sub (hInt P v)
  have hIntegral := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1) hGamma1 (hGammaP.add intervalIntegrable_const) hPoint
  rw [intervalIntegral.integral_add hGammaP intervalIntegrable_const,intervalIntegral.integral_const] at hIntegral
  simp only [sub_zero,one_smul] at hIntegral
  have hExact := averaged_original_power_jumps φ P κ u v h hSeparated.1 hv
  rw [hExact] at hIntegral
  have hError := mul_le_mul_of_nonneg_left hPadError (show 0 ≤ 2*W by positivity)
  change ε ≤ 2*W*u^(-(1:ℝ)/1000) at hError
  change averagedPowerDecrease φ κ h u v ≤ _ at hIntegral
  dsimp only [φ,P,v,W] at hIntegral hError ⊢
  linarith only [hIntegral,hError]

end
end StrongSilver
