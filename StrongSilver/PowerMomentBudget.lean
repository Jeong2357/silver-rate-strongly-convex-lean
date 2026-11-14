-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PowerLayerCake

namespace StrongSilver
open Real Set MeasureTheory
noncomputable section
set_option maxHeartbeats 2000000

/-- The rank bound controls a whole interval of pivot nu-powers with the
logarithmic cost used in the weighted refinement argument. -/
theorem powerMoment_rank_bound {A B cap : ℝ} (hA : 0 < A) (hAB : A ≤ B) (hcap : B ≤ cap) (h : List ℝ) :
    powerMoment h A B ≤ weightedCount h cap*(1+nu*Real.log (B/A)) := by
  let W := weightedCount h cap
  have hB := hA.trans_le hAB
  have hiInv : IntervalIntegrable (fun t : ℝ => t⁻¹) volume A B := by
    apply intervalIntegral.intervalIntegrable_inv ?_ continuousOn_id
    intro t ht
    rw [uIcc_of_le hAB] at ht
    exact (hA.trans_le ht.1).ne'
  have hiRight : IntervalIntegrable (fun t : ℝ => (nu*W)*t⁻¹) volume A B := hiInv.const_mul _
  have hi := intervalIntegral.integral_mono_on_of_le_Ioo hAB (power_weighted_count_integrable hA hAB h) hiRight (by
    intro t ht
    have ht0 := hA.trans ht.1
    have hcount := countAbove_rank_bound h ht0 (ht.2.le.trans hcap)
    have hk : 0 ≤ powerKernel t := mul_nonneg nu_positive.le (Real.rpow_pos_of_pos ht0 _).le
    have hh := mul_le_mul_of_nonneg_left hcount hk
    have hp : t^(nu-1)*t^(-nu) = t⁻¹ := by
      rw [← Real.rpow_add ht0,show nu-1+-nu = -1 by ring,Real.rpow_neg_one]
    have he : powerKernel t*(W*t^(-nu)) = (nu*W)*t⁻¹ := by
      calc
        _ = (nu*W)*(t^(nu-1)*t^(-nu)) := by unfold powerKernel; ring
        _ = _ := by rw [hp]
    exact hh.trans_eq he)
  rw [intervalIntegral.integral_const_mul,integral_inv_of_pos hA hB] at hi
  have hfirst := threshold_le_weightedCount h hA (hAB.trans hcap)
  rw [powerMoment_eq_layerCake hA hAB h]
  calc
    _ ≤ W+(nu*W)*Real.log (B/A) := add_le_add hfirst hi
    _ = _ := by ring

theorem powerMoment_log_bound {A B cap : ℝ} (hA : 0 < A) (hAB : A ≤ B) (hcap : B ≤ cap) (h : List ℝ) :
    powerMoment h A B ≤ weightedCount h cap*(1+Real.log (B/A)) := by
  have hh := powerMoment_rank_bound hA hAB hcap h
  have hlog := Real.log_nonneg ((one_le_div hA).mpr hAB)
  have hp := mul_nonneg (mul_nonneg (weightedCount_nonneg h cap) hlog) (sub_nonneg.mpr nu_lt_one.le)
  nlinarith only [hh,hp]

end
end StrongSilver
