-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CappedTransform
import Mathlib.Analysis.Complex.JensenFormula

namespace StrongSilver
open Complex Metric Real MeasureTheory MeromorphicOn
noncomputable section

theorem jensen_lower_unit {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (closedBall 0 1))
    (hzero : f 0 ≠ 0) :
    Real.log ‖f 0‖ ≤ circleAverage (fun z => Real.log ‖f z‖) 0 1 := by
  have hf' : AnalyticOnNhd ℂ f (closedBall 0 |(1 : ℝ)|) := by simpa only [abs_one] using hf
  have hform := hf'.circleAverage_log_norm (by norm_num : (1 : ℝ) ≠ 0) hzero
  rw [hform]
  have hsum : 0 ≤ ∑ᶠ u, (MeromorphicOn.divisor f (closedBall 0 |(1 : ℝ)|) u : ℝ)*
      Real.log (1*‖(0 : ℂ)-u‖⁻¹) := by
    apply finsum_nonneg
    intro u
    by_cases hu : u ∈ closedBall (0 : ℂ) |(1 : ℝ)|
    · have hd : (0 : ℝ) ≤ MeromorphicOn.divisor f (closedBall 0 |(1 : ℝ)|) u := by
        exact_mod_cast hf'.divisor_nonneg u
      apply mul_nonneg hd
      simp only [one_mul,zero_sub,norm_neg]
      by_cases hz : u = 0
      · simp [hz]
      · have hn : 0 < ‖u‖ := norm_pos_iff.mpr hz
        have hnu : ‖u‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right,abs_one] using hu
        exact Real.log_nonneg ((one_le_inv₀ hn).mpr hnu)
    · rw [(MeromorphicOn.divisor f (closedBall 0 |(1 : ℝ)|)).apply_eq_zero_of_notMem hu]
      simp
  linarith

def spectralPolynomial (r w : ℝ) (z : ℂ) : ℂ :=
  (r : ℂ)*z^2+((1+r^2-w : ℝ) : ℂ)*z+(r : ℂ)

def spectralAverage (r w : ℝ) : ℝ :=
  circleAverage (fun z => Real.log ‖spectralPolynomial r w z‖) 0 1

theorem spectralPolynomial_analytic (r w : ℝ) :
    AnalyticOnNhd ℂ (spectralPolynomial r w) (closedBall 0 1) := by
  intro z hz
  unfold spectralPolynomial
  fun_prop

theorem spectral_log_integrable (r w : ℝ) :
    CircleIntegrable (fun z => Real.log ‖spectralPolynomial r w z‖) 0 1 := by
  have hf : AnalyticOnNhd ℂ (spectralPolynomial r w) (sphere 0 |(1 : ℝ)|) := by
    intro z hz
    unfold spectralPolynomial
    fun_prop
  exact hf.meromorphicOn.circleIntegrable_log_norm

/-- The uniform logarithmic floor for the arcsine curvature average. -/
theorem spectralAverage_lower {r : ℝ} (hr : 0 < r) (w : ℝ) : Real.log r ≤ spectralAverage r w := by
  have hz : spectralPolynomial r w 0 ≠ 0 := by
    simp only [spectralPolynomial,zero_pow (by decide : 2 ≠ 0),mul_zero,add_zero,zero_add]
    exact Complex.ofReal_ne_zero.mpr hr.ne'
  have hh := jensen_lower_unit (spectralPolynomial_analytic r w) hz
  simpa only [spectralPolynomial,zero_pow (by decide : 2 ≠ 0),mul_zero,add_zero,zero_add,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr,spectralAverage] using hh

theorem spectralPolynomial_on_unit (r w : ℝ) (z : ℂ) (hz : ‖z‖ = 1) :
    spectralPolynomial r w z = ((1+r^2-w+2*r*z.re : ℝ) : ℂ)*z := by
  have hsq : z.re^2+z.im^2 = 1 := by
    have hh := Complex.sq_norm z
    rw [hz] at hh
    simp only [Complex.normSq_apply,one_pow] at hh
    nlinarith
  apply Complex.ext
  · simp only [spectralPolynomial,pow_two,Complex.add_re,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,Complex.mul_im,zero_mul,mul_zero,sub_zero,add_zero]
    linear_combination -r*hsq
  · simp only [spectralPolynomial,pow_two,Complex.add_im,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.mul_re,zero_mul,mul_zero,sub_zero,add_zero]
    ring

theorem spectral_norm_on_unit (r w : ℝ) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖spectralPolynomial r w z‖ = |1+r^2-w+2*r*z.re| := by
  rw [spectralPolynomial_on_unit r w z hz,norm_mul,Complex.norm_real,Real.norm_eq_abs,hz,mul_one]

theorem spectral_denominator_bounds {r : ℝ} (hr : 0 ≤ r) (z : ℂ) (hz : ‖z‖ = 1) :
    (1-r)^2 ≤ 1+r^2+2*r*z.re ∧ 1+r^2+2*r*z.re ≤ (1+r)^2 := by
  have hh := Complex.abs_re_le_norm z
  rw [hz] at hh
  obtain ⟨hl,hu⟩ := abs_le.mp hh
  have hmul : 0 ≤ 2*r := by positivity
  constructor
  · nlinarith only [mul_le_mul_of_nonneg_left hl hmul]
  · nlinarith only [mul_le_mul_of_nonneg_left hu hmul]

end
end StrongSilver
