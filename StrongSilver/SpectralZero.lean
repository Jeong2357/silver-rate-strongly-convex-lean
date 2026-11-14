-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.SpectralPotential

namespace StrongSilver
open Complex Metric Real MeasureTheory
noncomputable section

theorem spectralPolynomial_zero_factor {r : ℝ} (hr : r ≠ 0) (z : ℂ) :
    spectralPolynomial r 0 z = (r : ℂ)*(z+(r : ℂ))*(z+((r⁻¹ : ℝ) : ℂ)) := by
  have hrc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  unfold spectralPolynomial
  push_cast
  field_simp [hrc]
  ring

theorem unit_add_real_ne_zero {z : ℂ} (hz : ‖z‖ = 1) {r : ℝ} (hr : |r| ≠ 1) :
    z+(r : ℂ) ≠ 0 := by
  intro he
  have hze : z = -(r : ℂ) := eq_neg_of_add_eq_zero_left he
  rw [hze,norm_neg,Complex.norm_real,Real.norm_eq_abs] at hz
  exact hr hz

theorem spectral_zero_log_split {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (z : ℂ) (hz : ‖z‖ = 1) :
    Real.log ‖spectralPolynomial r 0 z‖ =
      Real.log r+Real.log ‖z+(r : ℂ)‖+Real.log ‖z+((r⁻¹ : ℝ) : ℂ)‖ := by
  have hri : 1 < r⁻¹ := (one_lt_inv₀ hr).mpr hr1
  have hz1 := unit_add_real_ne_zero hz (show |r| ≠ 1 by rw [abs_of_pos hr]; linarith)
  have hz2 := unit_add_real_ne_zero hz
    (show |r⁻¹| ≠ 1 by rw [abs_of_pos (inv_pos.mpr hr)]; linarith)
  rw [spectralPolynomial_zero_factor hr.ne',norm_mul,norm_mul,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos hr]
  rw [Real.log_mul (mul_pos hr (norm_pos_iff.mpr hz1)).ne' (norm_ne_zero_iff.mpr hz2),
    Real.log_mul hr.ne' (norm_ne_zero_iff.mpr hz1)]

theorem spectralAverage_zero {r : ℝ} (hr : 0 < r) (hr1 : r < 1) : spectralAverage r 0 = 0 := by
  have hI1 : CircleIntegrable (fun z : ℂ => Real.log ‖z+(r : ℂ)‖) 0 1 := by
    simpa only [sub_neg_eq_add] using
      (circleIntegrable_log_norm_sub_const (a := -(r : ℂ)) (c := 0) 1)
  have hI2 : CircleIntegrable (fun z : ℂ => Real.log ‖z+((r⁻¹ : ℝ) : ℂ)‖) 0 1 := by
    simpa only [sub_neg_eq_add] using
      (circleIntegrable_log_norm_sub_const (a := -((r⁻¹ : ℝ) : ℂ)) (c := 0) 1)
  have hA1 : circleAverage (fun z : ℂ => Real.log ‖z+(r : ℂ)‖) 0 1 = 0 := by
    have hnorm : ‖-(r : ℂ)‖ < 1 := by
      simpa only [norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr] using hr1
    simpa only [sub_neg_eq_add] using circleAverage_log_norm_sub_const₀ hnorm
  have hA2 : circleAverage (fun z : ℂ => Real.log ‖z+((r⁻¹ : ℝ) : ℂ)‖) 0 1 = Real.log r⁻¹ := by
    have hnorm : 1 < ‖-((r⁻¹ : ℝ) : ℂ)‖ := by
      simpa only [norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)] using
        (one_lt_inv₀ hr).mpr hr1
    simpa only [sub_neg_eq_add,norm_neg,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr)] using circleAverage_log_norm_sub_const₂ hnorm
  unfold spectralAverage
  calc
    _ = circleAverage (fun z : ℂ => Real.log r+Real.log ‖z+(r : ℂ)‖+
        Real.log ‖z+((r⁻¹ : ℝ) : ℂ)‖) 0 1 := by
      apply circleAverage_congr_sphere
      intro z hz
      have hzn : ‖z‖ = 1 := by simpa only [mem_sphere,dist_zero_right,abs_one] using hz
      exact spectral_zero_log_split hr hr1 z hzn
    _ = Real.log r+0+Real.log r⁻¹ := by
      change circleAverage
        (((fun _ : ℂ => Real.log r)+(fun z : ℂ => Real.log ‖z+(r : ℂ)‖))+
          (fun z : ℂ => Real.log ‖z+((r⁻¹ : ℝ) : ℂ)‖)) 0 1 = _
      rw [circleAverage_add ((circleIntegrable_const (Real.log r) 0 1).add hI1) hI2,
        circleAverage_add (circleIntegrable_const (Real.log r) 0 1) hI1,
        circleAverage_const,hA1,hA2]
    _ = 0 := by rw [Real.log_inv]; ring

end
end StrongSilver
