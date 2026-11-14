-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.SmoothedBandWeight
import StrongSilver.ExponentialStepIntegral

namespace StrongSilver
open Real Set MeasureTheory
noncomputable section
set_option maxHeartbeats 6000000

theorem unitStep_integrable (c a b : ℝ) : IntervalIntegrable (fun t : ℝ => if t < c then (1:ℝ) else 0) volume a b := by
  simpa only [zero_mul,Real.exp_zero] using exponential_step_intervalIntegrable 0 c a b

/-- The exact distribution function of the uniform smoothing window. -/
theorem unitStep_integral (c : ℝ) : (∫ t in (0:ℝ)..1, if t < c then (1:ℝ) else 0) = min 1 (max 0 c) := by
  by_cases hc0 : c ≤ 0
  · have he : (∫ t in (0:ℝ)..1, if t < c then (1:ℝ) else 0) = ∫ _t in (0:ℝ)..1, (0:ℝ) := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro t ht
      exact if_neg (not_lt_of_ge (hc0.trans ht.1.le))
    rw [he]
    simp only [max_eq_left hc0,min_eq_right (by norm_num : (0:ℝ) ≤ 1),intervalIntegral.integral_zero]
  · have hc : 0 < c := lt_of_not_ge hc0
    by_cases hc1 : 1 ≤ c
    · have he : (∫ t in (0:ℝ)..1, if t < c then (1:ℝ) else 0) = ∫ _t in (0:ℝ)..1, (1:ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
        intro t ht
        exact if_pos (ht.2.trans_le hc1)
      rw [he]
      simp only [max_eq_right hc.le,min_eq_left hc1,intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_one]
    · have hc' : c < 1 := lt_of_not_ge hc1
      have hLeft : (∫ t in (0:ℝ)..c, if t < c then (1:ℝ) else 0) = c := by
        calc
          _ = ∫ _t in (0:ℝ)..c, (1:ℝ) := by
            apply intervalIntegral.integral_congr_Ioo_of_le hc.le
            intro t ht
            exact if_pos ht.2
          _ = c := by simp
      have hRight : (∫ t in c..(1:ℝ), if t < c then (1:ℝ) else 0) = 0 := by
        calc
          _ = ∫ _t in c..(1:ℝ), (0:ℝ) := by
            apply intervalIntegral.integral_congr_Ioo_of_le hc'.le
            intro t ht
            exact if_neg (not_lt_of_ge ht.1.le)
          _ = 0 := by simp
      rw [← intervalIntegral.integral_add_adjacent_intervals (unitStep_integrable c 0 c) (unitStep_integrable c c 1),hLeft,hRight]
      simp only [max_eq_right hc.le,min_eq_right hc'.le,add_zero]

theorem thresholdRamp_integral {u : ℝ} (hu : 0 < u) (s : ℝ) :
    thresholdRamp u s = ∫ t in (0:ℝ)..1, if u+t*Real.sqrt u < s then (1:ℝ) else 0 := by
  have he : (fun t : ℝ => if u+t*Real.sqrt u < s then (1:ℝ) else 0) =
      fun t : ℝ => if t < (s-u)/Real.sqrt u then (1:ℝ) else 0 := by
    funext t
    have hi : u+t*Real.sqrt u < s ↔ t < (s-u)/Real.sqrt u := by
      rw [lt_div_iff₀ (Real.sqrt_pos.mpr hu)]
      constructor <;> intro hh <;> linarith only [hh]
    simp only [hi]
  rw [he,unitStep_integral]
  rfl

theorem smoothedThresholdIndicator_integrable {u : ℝ} (hu : 0 < u) (s a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => if u+t*Real.sqrt u < s then (1:ℝ) else 0) volume a b := by
  have he : (fun t : ℝ => if u+t*Real.sqrt u < s then (1:ℝ) else 0) =
      fun t : ℝ => if t < (s-u)/Real.sqrt u then (1:ℝ) else 0 := by
    funext t
    have hi : u+t*Real.sqrt u < s ↔ t < (s-u)/Real.sqrt u := by
      rw [lt_div_iff₀ (Real.sqrt_pos.mpr hu)]
      constructor <;> intro hh <;> linarith only [hh]
    simp only [hi]
  rw [he]
  exact unitStep_integrable _ _ _

/-- Exact averaged original-threshold inclusion weight. -/
theorem smoothedBandWeight_integral {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (s : ℝ) :
    smoothedBandWeight u v s = ∫ t in (0:ℝ)..1,
      ((if v+t*Real.sqrt v < s then (1:ℝ) else 0)-(if u+t*Real.sqrt u < s then (1:ℝ) else 0)) := by
  rw [intervalIntegral.integral_sub (smoothedThresholdIndicator_integrable hv s 0 1) (smoothedThresholdIndicator_integrable hu s 0 1),
    ← thresholdRamp_integral hv s,← thresholdRamp_integral hu s]
  rfl

end
end StrongSilver
