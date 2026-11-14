-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CappedTransform
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic

namespace StrongSilver
open Set MeasureTheory
noncomputable section

def quadraticLogIntegral (x : ℝ) : ℝ := ∫ t in (2 : ℝ)..4, Real.log (1-x*t)
def logPrimitive (x : ℝ) : ℝ := x*Real.log x-x

theorem quadratic_log_integrable (x a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => Real.log (1-x*t)) volume a b := by
  have ha : AnalyticOnNhd ℝ (fun t : ℝ => 1-x*t) (Set.uIcc a b) := by
    intro t ht
    fun_prop
  simpa only [Function.comp_def] using ha.meromorphicOn.intervalIntegrable_log

theorem quadraticLogIntegral_formula {x : ℝ} (hx : x ≠ 0) :
    quadraticLogIntegral x = x⁻¹*(logPrimitive (1-2*x)-logPrimitive (1-4*x)) := by
  unfold quadraticLogIntegral logPrimitive
  rw [intervalIntegral.integral_comp_sub_mul Real.log hx 1,integral_log]
  simp only [smul_eq_mul]
  ring

theorem quadraticLogIntegral_small {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1/8) :
    -16*x ≤ quadraticLogIntegral x := by
  have hpoint (t : ℝ) (ht : t ∈ Icc (2 : ℝ) 4) : -8*x ≤ Real.log (1-x*t) := by
    have h0 : 0 ≤ x*t := mul_nonneg hx (by linarith [ht.1])
    have h4 : x*t ≤ 4*x := by nlinarith only [mul_le_mul_of_nonneg_left ht.2 hx]
    have hhalf : x*t ≤ 1/2 := by linarith
    have hl := log_one_sub_defect hhalf
    have hp : 0 ≤ (x*t)*(1-2*(x*t)) := mul_nonneg h0 (by linarith)
    nlinarith only [hl,hp,h4]
  have hI := intervalIntegral.integral_mono_on (by norm_num : (2 : ℝ) ≤ 4)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => -8*x) volume 2 4)
    (quadratic_log_integrable x 2 4) hpoint
  simpa only [intervalIntegral.integral_const,smul_eq_mul,show (4 : ℝ)-2=2 by norm_num,
    show (2 : ℝ)*(-8*x)=-16*x by ring,quadraticLogIntegral] using hI

/-- Uniform logarithmic loss for a positive step below the averaging scale. -/
theorem quadraticLogIntegral_lower : ∃ C > 0, ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
    -C*x ≤ quadraticLogIntegral x := by
  have hc : Continuous logPrimitive := Real.continuous_mul_log.sub continuous_id
  obtain ⟨M0,hM0⟩ := (isCompact_Icc : IsCompact (Icc (-3 : ℝ) 1)).exists_bound_of_continuousOn
    hc.continuousOn
  let M := max M0 1
  have hM : 1 ≤ M := le_max_right _ _
  have hbound (u : ℝ) (hu : u ∈ Icc (-3 : ℝ) 1) : |logPrimitive u| ≤ M := by
    have hh : |logPrimitive u| ≤ M0 := by simpa only [Real.norm_eq_abs] using hM0 u hu
    exact hh.trans (le_max_left _ _)
  refine ⟨128*M,by positivity,fun x hx hx1 => ?_⟩
  by_cases hsmall : x ≤ 1/8
  · have hh := quadraticLogIntegral_small hx hsmall
    have hC : 16 ≤ 128*M := by linarith
    nlinarith only [hh,mul_le_mul_of_nonneg_right hC hx]
  · have hxpos : 0 < x := by linarith
    have hb1 := hbound (1-2*x) ⟨by linarith,by linarith⟩
    have hb2 := hbound (1-4*x) ⟨by linarith,by linarith⟩
    have hdiff : -2*M ≤ logPrimitive (1-2*x)-logPrimitive (1-4*x) := by
      have h1 := (abs_le.mp hb1).1
      have h2 := (abs_le.mp hb2).2
      linarith
    have hform := quadraticLogIntegral_formula hxpos.ne'
    have hmul : x*quadraticLogIntegral x = logPrimitive (1-2*x)-logPrimitive (1-4*x) := by
      rw [hform,← mul_assoc,mul_inv_cancel₀ hxpos.ne',one_mul]
    have hquad : 2*M ≤ 128*M*x*x := by
      have hs : (1 : ℝ)/8 ≤ x := le_of_lt (lt_of_not_ge hsmall)
      have hsq : (1 : ℝ)/64 ≤ x*x := by nlinarith
      nlinarith only [mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 128*M)]
    apply (mul_le_mul_iff_right₀ hxpos).mp
    nlinarith only [hdiff,hmul,hquad]

theorem quadraticLogIntegral_large {x : ℝ} (hx : 1 ≤ x) :
    2*Real.log x ≤ quadraticLogIntegral x := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hpoint (t : ℝ) (ht : t ∈ Icc (2 : ℝ) 4) : Real.log x ≤ Real.log (1-x*t) := by
    have hmul := mul_le_mul_of_nonneg_left ht.1 hxpos.le
    have hxt : x ≤ x*t-1 := by nlinarith only [hmul,hx]
    calc
      Real.log x ≤ Real.log (x*t-1) := Real.log_le_log hxpos hxt
      _ = Real.log (1-x*t) := by rw [show x*t-1 = -(1-x*t) by ring,Real.log_neg_eq_log]
  have hI := intervalIntegral.integral_mono_on (by norm_num : (2 : ℝ) ≤ 4)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => Real.log x) volume 2 4)
    (quadratic_log_integrable x 2 4) hpoint
  simpa only [intervalIntegral.integral_const,smul_eq_mul,show (4 : ℝ)-2=2 by norm_num,
    quadraticLogIntegral] using hI

theorem quadraticLogIntegral_negative {x : ℝ} (hx : x ≤ 0) :
    2*Real.log (1-x) ≤ quadraticLogIntegral x := by
  have hpoint (t : ℝ) (ht : t ∈ Icc (2 : ℝ) 4) : Real.log (1-x) ≤ Real.log (1-x*t) := by
    apply Real.log_le_log (by linarith : 0 < 1-x)
    have ht1 : 1 ≤ t := by linarith [ht.1]
    have hmul := mul_le_mul_of_nonpos_left ht1 hx
    linarith
  have hI := intervalIntegral.integral_mono_on (by norm_num : (2 : ℝ) ≤ 4)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => Real.log (1-x)) volume 2 4)
    (quadratic_log_integrable x 2 4) hpoint
  simpa only [intervalIntegral.integral_const,smul_eq_mul,show (4 : ℝ)-2=2 by norm_num,
    quadraticLogIntegral] using hI

end
end StrongSilver
