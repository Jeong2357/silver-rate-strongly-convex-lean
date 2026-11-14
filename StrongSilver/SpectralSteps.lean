-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.SpectralConcavity

namespace StrongSilver
open Complex Metric Real MeasureTheory Filter
noncomputable section

def spectralStepLog (r B h : ℝ) (z : ℂ) : ℝ :=
  Real.log ‖spectralPolynomial r (h*(1-r)^2/B) z‖-
    Real.log ‖spectralPolynomial r 0 z‖

theorem spectralStepLog_integrable (r B h : ℝ) : CircleIntegrable (spectralStepLog r B h) 0 1 :=
  (spectral_log_integrable r _).sub (spectral_log_integrable r 0)

theorem spectralStepLog_average {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (B h : ℝ) :
    circleAverage (spectralStepLog r B h) 0 1 = spectralAverage r (h*(1-r)^2/B) := by
  change circleAverage ((fun z => Real.log ‖spectralPolynomial r (h*(1-r)^2/B) z‖)-
    (fun z => Real.log ‖spectralPolynomial r 0 z‖)) 0 1 = _
  rw [circleAverage_sub (spectral_log_integrable r _) (spectral_log_integrable r 0)]
  change spectralAverage r (h*(1-r)^2/B)-spectralAverage r 0 = _
  rw [spectralAverage_zero hr hr1,sub_zero]

theorem spectralStepLog_on_unit {r B h : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (hB : 0 < B)
    {z : ℂ} (hz : ‖z‖ = 1) (hn : spectralPolynomial r (h*(1-r)^2/B) z ≠ 0) :
    spectralStepLog r B h z = Real.log (1-h*spectralCurvature r B z) := by
  have hd := spectralDenominator_positive hr hr1 z hz
  have hp : spectralDenominator r z-h*(1-r)^2/B ≠ 0 := by
    intro he
    apply hn
    apply norm_eq_zero.mp
    rw [spectral_norm_on_unit r _ z hz]
    have hid : 1+r^2-h*(1-r)^2/B+2*r*z.re = spectralDenominator r z-h*(1-r)^2/B := by
      unfold spectralDenominator
      ring
    rw [hid,he,abs_zero]
  unfold spectralStepLog
  rw [spectral_log_on_unit (w := 0) hz (by simpa only [sub_zero] using hd.le),sub_zero]
  rw [spectral_norm_on_unit r _ z hz]
  have hid : 1+r^2-h*(1-r)^2/B+2*r*z.re = spectralDenominator r z-h*(1-r)^2/B := by
    unfold spectralDenominator
    ring
  rw [hid,Real.log_abs,← Real.log_div hp hd.ne']
  congr 1
  unfold spectralCurvature
  field_simp
  <;> ring

theorem spectralStepLog_lower_small {r B h : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hB : 0 < B) (hh : 0 ≤ h) (hhB : h ≤ B) :
    (h/B)*Real.log r ≤ circleAverage (spectralStepLog r B h) 0 1 := by
  rw [spectralStepLog_average hr hr1]
  have he : h*(1-r)^2/B = (h/B)*(1-r)^2 := by ring
  rw [he]
  exact spectralAverage_small_lower hr hr1 (div_nonneg hh hB.le) ((div_le_one hB).mpr hhB)

theorem spectralStepLog_lower_floor {r B h : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    Real.log r ≤ circleAverage (spectralStepLog r B h) 0 1 := by
  rw [spectralStepLog_average hr hr1]
  exact spectralAverage_lower hr _

end
end StrongSilver
