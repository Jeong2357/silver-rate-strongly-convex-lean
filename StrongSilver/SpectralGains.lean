-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.SpectralSchedule
import StrongSilver.LayerCake

namespace StrongSilver
open Complex Metric Real MeasureTheory Filter
noncomputable section

theorem spectralStepLog_lower_negative {r B κ h : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hB : 0 < B) (hκ : 0 < κ) (hh : h ≤ 0)
    (hcurv : ∀ z : ℂ, ‖z‖ = 1 → 1/κ ≤ spectralCurvature r B z) :
    Real.log (1-h/κ) ≤ circleAverage (spectralStepLog r B h) 0 1 := by
  have he : ∀ᶠ z in codiscreteWithin (sphere (0 : ℂ) |(1 : ℝ)|),
      Real.log (1-h/κ) ≤ spectralStepLog r B h z := by
    filter_upwards [self_mem_codiscreteWithin (sphere (0 : ℂ) |(1 : ℝ)|),
      spectral_nonzero_codiscrete hr.ne' (h*(1-r)^2/B)] with z hz hn
    have hzn : ‖z‖ = 1 := by simpa only [mem_sphere,dist_zero_right,abs_one] using hz
    rw [spectralStepLog_on_unit hr.le hr1 hB hzn hn]
    have hp : 0 < 1-h/κ := by have hd := div_nonpos_of_nonpos_of_nonneg hh hκ.le; linarith
    apply Real.log_le_log hp
    have hm := mul_le_mul_of_nonpos_left (hcurv z hzn) hh
    simp only [div_eq_mul_inv,one_mul] at hm ⊢
    linarith
  have havg := circleAverage_mono_codiscrete_unit (circleIntegrable_const (Real.log (1-h/κ)) 0 1)
    (spectralStepLog_integrable r B h) he
  simpa only [circleAverage_const] using havg

theorem spectralStepLog_lower_large {r B κ h : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hB : 0 < B) (hκ : 0 < κ) (hh : κ/2 ≤ h)
    (hcurv : ∀ z : ℂ, ‖z‖ = 1 → 8/κ ≤ spectralCurvature r B z) :
    Real.log 3 ≤ circleAverage (spectralStepLog r B h) 0 1 := by
  have he : ∀ᶠ z in codiscreteWithin (sphere (0 : ℂ) |(1 : ℝ)|),
      Real.log 3 ≤ spectralStepLog r B h z := by
    filter_upwards [self_mem_codiscreteWithin (sphere (0 : ℂ) |(1 : ℝ)|),
      spectral_nonzero_codiscrete hr.ne' (h*(1-r)^2/B)] with z hz hn
    have hzn : ‖z‖ = 1 := by simpa only [mem_sphere,dist_zero_right,abs_one] using hz
    rw [spectralStepLog_on_unit hr.le hr1 hB hzn hn]
    have hh0 : 0 ≤ h := (by positivity : 0 ≤ κ/2).trans hh
    have hm := mul_le_mul_of_nonneg_left (hcurv z hzn) hh0
    have hfour : 4 ≤ h*(8/κ) := by
      rw [← mul_div_assoc]
      exact (le_div_iff₀ hκ).mpr (by linarith)
    have hfac : 1-h*spectralCurvature r B z ≤ -3 := by linarith
    calc
      Real.log 3 ≤ Real.log |1-h*spectralCurvature r B z| :=
        Real.log_le_log (by norm_num) (by rw [abs_of_nonpos (by linarith)]; linarith)
      _ = Real.log (1-h*spectralCurvature r B z) := Real.log_abs _
  have havg := circleAverage_mono_codiscrete_unit (circleIntegrable_const (Real.log 3) 0 1)
    (spectralStepLog_integrable r B h) he
  simpa only [circleAverage_const] using havg

theorem arcsineStepLog_lower_capped {a B h : ℝ} (ha : 0 < a) (ha1 : a ≤ 1/128)
    (hB : 0 < B) (hh : 0 ≤ h) :
    -9*Real.sqrt a*(max 0 (min h B)/B) ≤
      circleAverage (spectralStepLog (arcsineParameter a) B h) 0 1 := by
  obtain ⟨hr,hr1⟩ := arcsineParameter_bounds ha ha1
  have hlog := arcsine_parameter_log_bound ha ha1
  by_cases hhB : h ≤ B
  · have hb := spectralStepLog_lower_small hr hr1 hB hh hhB
    have hm := mul_le_mul_of_nonneg_left hlog (div_nonneg hh hB.le)
    rw [min_eq_left hhB,max_eq_right hh]
    nlinarith only [hb,hm]
  · have hb := spectralStepLog_lower_floor (B := B) (h := h) hr hr1
    rw [min_eq_right (le_of_not_ge hhB),max_eq_right hB.le,div_self hB.ne',mul_one]
    exact hlog.trans hb

end
end StrongSilver
