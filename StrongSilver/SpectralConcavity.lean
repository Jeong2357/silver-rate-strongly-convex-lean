-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ArcsineParameters
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

namespace StrongSilver
open Complex Metric Real MeasureTheory Filter
noncomputable section

theorem circleAverage_mono_codiscrete_unit {f g : ℂ → ℝ}
    (hf : CircleIntegrable f 0 1) (hg : CircleIntegrable g 0 1)
    (hfg : ∀ᶠ z in codiscreteWithin (sphere (0 : ℂ) |(1 : ℝ)|), f z ≤ g z) :
    circleAverage f 0 1 ≤ circleAverage g 0 1 := by
  unfold circleAverage
  simp only [smul_eq_mul]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr Real.two_pi_pos.le)
  apply intervalIntegral.integral_mono_ae_restrict (le_of_lt Real.two_pi_pos) hf hg
  apply ae_restrict_le_codiscreteWithin measurableSet_Icc
  have hc : ∀ᶠ t in codiscrete ℝ, f (circleMap 0 1 t) ≤ g (circleMap 0 1 t) :=
    circleMap_preimage_codiscrete (by norm_num : (1 : ℝ) ≠ 0) hfg
  exact ((codiscreteWithin_le_codiscrete_inf_principal _).trans inf_le_left) hc

theorem spectral_log_on_unit {r w : ℝ} {z : ℂ} (hz : ‖z‖ = 1)
    (hw : 0 ≤ spectralDenominator r z-w) :
    Real.log ‖spectralPolynomial r w z‖ = Real.log (spectralDenominator r z-w) := by
  rw [spectral_norm_on_unit r w z hz]
  have he : 1+r^2-w+2*r*z.re = spectralDenominator r z-w := by unfold spectralDenominator; ring
  rw [he,abs_of_nonneg hw]

theorem spectral_nonzero_codiscrete {r : ℝ} (hr : r ≠ 0) (w : ℝ) :
    ∀ᶠ z in codiscreteWithin (sphere (0 : ℂ) |(1 : ℝ)|), spectralPolynomial r w z ≠ 0 := by
  have ha : AnalyticOnNhd ℂ (spectralPolynomial r w) Set.univ := by
    intro z hz
    unfold spectralPolynomial
    fun_prop
  have hz : spectralPolynomial r w 0 ≠ 0 := by simpa [spectralPolynomial] using Complex.ofReal_ne_zero.mpr hr
  have he := ha.preimage_zero_mem_codiscrete hz
  have hwithin : codiscreteWithin (sphere (0 : ℂ) |(1 : ℝ)|) ≤ codiscrete ℂ :=
    (codiscreteWithin_le_codiscrete_inf_principal _).trans inf_le_left
  apply hwithin
  filter_upwards [he] with z hz
  simpa only [Set.mem_compl_iff,Set.mem_preimage,Set.mem_singleton_iff] using hz

/-- Concavity gives the linear loss below the cap without differentiating under an integral. -/
theorem spectralAverage_small_lower {r θ : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) : θ*Real.log r ≤ spectralAverage r (θ*(1-r)^2) := by
  let m := (1-r)^2
  let f0 : ℂ → ℝ := fun z => Real.log ‖spectralPolynomial r 0 z‖
  let f1 : ℂ → ℝ := fun z => Real.log ‖spectralPolynomial r m z‖
  let fmix : ℂ → ℝ := fun z => (1-θ)*f0 z+θ*f1 z
  have h0 : CircleIntegrable f0 0 1 := spectral_log_integrable r 0
  have h1 : CircleIntegrable f1 0 1 := spectral_log_integrable r m
  have h0mul : CircleIntegrable (fun z => (1-θ)*f0 z) 0 1 :=
    IntervalIntegrable.const_mul h0 (1-θ)
  have h1mul : CircleIntegrable (fun z => θ*f1 z) 0 1 := IntervalIntegrable.const_mul h1 θ
  have hmix : CircleIntegrable fmix 0 1 := by
    change CircleIntegrable ((fun z => (1-θ)*f0 z)+(fun z => θ*f1 z)) 0 1
    exact h0mul.add h1mul
  have he : ∀ᶠ z in codiscreteWithin (sphere (0 : ℂ) |(1 : ℝ)|),
      fmix z ≤ Real.log ‖spectralPolynomial r (θ*m) z‖ := by
    filter_upwards [self_mem_codiscreteWithin (sphere (0 : ℂ) |(1 : ℝ)|),
      spectral_nonzero_codiscrete hr.ne' m] with z hz hn
    have hzn : ‖z‖ = 1 := by simpa only [mem_sphere,dist_zero_right,abs_one] using hz
    have hd := spectralDenominator_positive hr.le hr1 z hzn
    have hm0 : 0 ≤ spectralDenominator r z-m :=
      sub_nonneg.mpr (spectral_denominator_bounds hr.le z hzn).1
    have hmne : spectralDenominator r z-m ≠ 0 := by
      intro hz0
      apply hn
      apply norm_eq_zero.mp
      rw [spectral_norm_on_unit r m z hzn]
      have hid : 1+r^2-m+2*r*z.re = spectralDenominator r z-m := by unfold spectralDenominator; ring
      rw [hid,hz0,abs_zero]
    have hmpos : 0 < spectralDenominator r z-m := lt_of_le_of_ne hm0 hmne.symm
    have hmiddle : 0 ≤ spectralDenominator r z-θ*m := by
      have hm : 0 ≤ m := sq_nonneg _
      nlinarith only [hm0,mul_le_mul_of_nonneg_right hθ1 hm]
    have hc := strictConcaveOn_log_Ioi.concaveOn.2 hd hmpos
      (sub_nonneg.mpr hθ1) hθ (show (1-θ)+θ=1 by ring)
    have hid : (1-θ)*spectralDenominator r z+θ*(spectralDenominator r z-m) =
        spectralDenominator r z-θ*m := by ring
    simp only [smul_eq_mul] at hc
    rw [hid] at hc
    have hlog0 : f0 z = Real.log (spectralDenominator r z) := by
      dsimp [f0]
      simpa only [sub_zero] using
        (spectral_log_on_unit (r := r) (w := 0) hzn (by simpa only [sub_zero] using hd.le))
    simpa only [fmix,hlog0,f1,
      spectral_log_on_unit hzn hm0,spectral_log_on_unit hzn hmiddle,sub_zero] using hc
  have havg := circleAverage_mono_codiscrete_unit hmix (spectral_log_integrable r (θ*m)) he
  have havgmix : circleAverage fmix 0 1 = (1-θ)*spectralAverage r 0+θ*spectralAverage r m := by
    change circleAverage ((fun z => (1-θ)*f0 z)+(fun z => θ*f1 z)) 0 1 = _
    rw [circleAverage_add h0mul h1mul]
    change circleAverage ((1-θ) • f0) 0 1+circleAverage (θ • f1) 0 1 = _
    rw [circleAverage_smul,circleAverage_smul]
    rfl
  rw [havgmix,spectralAverage_zero hr hr1,mul_zero,zero_add] at havg
  have hlower := mul_le_mul_of_nonneg_left (spectralAverage_lower hr m) hθ
  exact hlower.trans havg

end
end StrongSilver
