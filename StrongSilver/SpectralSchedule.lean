-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.SpectralSteps
import StrongSilver.ErrorBounds

namespace StrongSilver
open Complex Metric Real MeasureTheory Filter
noncomputable section

def spectralScheduleLog (r B : ℝ) (h : List ℝ) (z : ℂ) : ℝ :=
  (h.map (fun b => spectralStepLog r B b z)).sum

theorem spectralScheduleLog_integrable (r B : ℝ) (h : List ℝ) :
    CircleIntegrable (spectralScheduleLog r B h) 0 1 := by
  induction h with
  | nil => exact circleIntegrable_const 0 0 1
  | cons b h ih =>
    change CircleIntegrable ((spectralStepLog r B b)+(spectralScheduleLog r B h)) 0 1
    exact (spectralStepLog_integrable r B b).add ih

theorem spectralScheduleLog_average (r B : ℝ) (h : List ℝ) :
    circleAverage (spectralScheduleLog r B h) 0 1 =
      (h.map (fun b => circleAverage (spectralStepLog r B b) 0 1)).sum := by
  induction h with
  | nil => exact circleAverage_const 0 0 1
  | cons b h ih =>
    change circleAverage ((spectralStepLog r B b)+(spectralScheduleLog r B h)) 0 1 = _
    rw [circleAverage_add (spectralStepLog_integrable r B b) (spectralScheduleLog_integrable r B h),ih]
    rfl

theorem spectral_factors_codiscrete {r : ℝ} (hr : r ≠ 0) (B : ℝ) (h : List ℝ) :
    ∀ᶠ z in codiscreteWithin (sphere (0 : ℂ) |(1 : ℝ)|),
      ∀ b ∈ h, spectralPolynomial r (b*(1-r)^2/B) z ≠ 0 := by
  induction h with
  | nil => simp
  | cons b h ih =>
    filter_upwards [spectral_nonzero_codiscrete hr (b*(1-r)^2/B),ih] with z hb hh
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hb
    · exact hh c hc

theorem spectral_factor_ne_zero {r B b : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (hB : 0 < B)
    {z : ℂ} (hz : ‖z‖ = 1) (hn : spectralPolynomial r (b*(1-r)^2/B) z ≠ 0) :
    1-b*spectralCurvature r B z ≠ 0 := by
  have hd := spectralDenominator_positive hr hr1 z hz
  have he : 1-b*spectralCurvature r B z =
      (spectralDenominator r z-b*(1-r)^2/B)/spectralDenominator r z := by
    unfold spectralCurvature
    field_simp
    <;> ring
  rw [he]
  apply div_ne_zero _ hd.ne'
  intro he
  apply hn
  apply norm_eq_zero.mp
  rw [spectral_norm_on_unit r _ z hz]
  have hid : 1+r^2-b*(1-r)^2/B+2*r*z.re = spectralDenominator r z-b*(1-r)^2/B := by
    unfold spectralDenominator
    ring
  rw [hid,he,abs_zero]

theorem spectralScheduleLog_eq_log {r B : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (hB : 0 < B)
    (h : List ℝ) {z : ℂ} (hz : ‖z‖ = 1)
    (hn : ∀ b ∈ h, spectralPolynomial r (b*(1-r)^2/B) z ≠ 0) :
    spectralScheduleLog r B h z = Real.log (quadraticMultiplier (spectralCurvature r B z) h) := by
  have hf : ∀ x ∈ h.map (fun b => 1-(spectralCurvature r B z)*b), x ≠ 0 := by
    intro x hx
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx
    simpa only [mul_comm] using spectral_factor_ne_zero hr hr1 hB hz (hn b hb)
  rw [quadraticMultiplier,Real.log_list_prod hf,List.map_map]
  unfold spectralScheduleLog
  congr 1
  apply List.map_congr_left
  intro b hb
  simpa only [Function.comp_def,mul_comm] using spectralStepLog_on_unit hr hr1 hB hz (hn b hb)

theorem spectralScheduleLog_le_distance {r B κ : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hB : 0 < B) (hκ : 0 < κ)
    (hcurv : ∀ z : ℂ, ‖z‖ = 1 → 1/κ ≤ spectralCurvature r B z ∧ spectralCurvature r B z ≤ 1)
    (h : List ℝ) :
    circleAverage (spectralScheduleLog r B h) 0 1 ≤ Real.log (D κ h).toReal/2 := by
  have he : ∀ᶠ z in codiscreteWithin (sphere (0 : ℂ) |(1 : ℝ)|),
      spectralScheduleLog r B h z ≤ Real.log (D κ h).toReal/2 := by
    filter_upwards [self_mem_codiscreteWithin (sphere (0 : ℂ) |(1 : ℝ)|),
      spectral_factors_codiscrete hr.ne' B h] with z hz hn
    have hzn : ‖z‖ = 1 := by simpa only [mem_sphere,dist_zero_right,abs_one] using hz
    obtain ⟨hl,hu⟩ := hcurv z hzn
    have hq := quadratic_distance_lower κ (spectralCurvature r B z) hκ hl hu h
    have hqr := ENNReal.toReal_mono (D_ne_top κ h) hq
    rw [ENNReal.toReal_ofReal (sq_nonneg _)] at hqr
    have hqn : quadraticMultiplier (spectralCurvature r B z) h ≠ 0 := by
      apply List.prod_ne_zero
      intro ht
      obtain ⟨b,hb,he⟩ := List.mem_map.mp ht
      exact spectral_factor_ne_zero hr.le hr1 hB hzn (hn b hb) (by simpa only [mul_comm] using he)
    have hlog := Real.log_le_log ((sq_pos_iff).mpr hqn) hqr
    rw [Real.log_pow,← spectralScheduleLog_eq_log hr.le hr1 hB h hzn hn] at hlog
    norm_num at hlog
    linarith
  have havg := circleAverage_mono_codiscrete_unit (spectralScheduleLog_integrable r B h)
    (circleIntegrable_const (Real.log (D κ h).toReal/2) 0 1) he
  simpa only [circleAverage_const] using havg

end
end StrongSilver
