-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.SpectralZero

namespace StrongSilver
noncomputable section

def spectralDenominator (r : ℝ) (z : ℂ) : ℝ := 1+r^2+2*r*z.re
def spectralCurvature (r B : ℝ) (z : ℂ) : ℝ := (1-r)^2/(B*spectralDenominator r z)
def arcsineParameter (a : ℝ) : ℝ := (1-Real.sqrt (8*a))/(1+Real.sqrt (8*a))

theorem spectralDenominator_positive {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (z : ℂ) (hz : ‖z‖ = 1) : 0 < spectralDenominator r z := by
  have hh := (spectral_denominator_bounds hr z hz).1
  have hp : 0 < (1-r)^2 := sq_pos_of_pos (by linarith)
  exact hp.trans_le hh

theorem spectralCurvature_bounds {r B : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (hB : 0 < B)
    (z : ℂ) (hz : ‖z‖ = 1) :
    (1-r)^2/(B*(1+r)^2) ≤ spectralCurvature r B z ∧ spectralCurvature r B z ≤ 1/B := by
  obtain ⟨hl,hu⟩ := spectral_denominator_bounds hr z hz
  have hden := spectralDenominator_positive hr hr1 z hz
  have hp : 0 < (1-r)^2 := sq_pos_of_pos (by linarith)
  constructor
  · exact div_le_div_of_nonneg_left hp.le (mul_pos hB hden)
      (mul_le_mul_of_nonneg_left hu hB.le)
  · apply (div_le_div_iff₀ (mul_pos hB hden) hB).mpr
    change (1-r)^2*B ≤ 1*(B*(1+r^2+2*r*z.re))
    nlinarith only [mul_le_mul_of_nonneg_left hl hB.le]

theorem arcsineParameter_bounds {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1/128) :
    0 < arcsineParameter a ∧ arcsineParameter a < 1 := by
  have hspos : 0 < Real.sqrt (8*a) := Real.sqrt_pos.2 (by positivity)
  have hs := Real.sq_sqrt (by positivity : 0 ≤ 8*a)
  have hs1 : Real.sqrt (8*a) < 1 := by nlinarith
  constructor
  · exact div_pos (by linarith) (by positivity)
  · exact (div_lt_one (by positivity : 0 < 1+Real.sqrt (8*a))).mpr (by linarith)

theorem arcsine_ratio {a : ℝ} (ha : 0 ≤ a) :
    (1-arcsineParameter a)/(1+arcsineParameter a) = Real.sqrt (8*a) := by
  have hs := Real.sq_sqrt (by positivity : 0 ≤ 8*a)
  have hspos := Real.sqrt_nonneg (8*a)
  unfold arcsineParameter
  field_simp <;> ring

theorem arcsine_curvature_lower {a κ : ℝ} (ha : 0 < a) (ha1 : a ≤ 1/128) (hκ : 0 < κ)
    (z : ℂ) (hz : ‖z‖ = 1) : 8/κ ≤ spectralCurvature (arcsineParameter a) (a*κ) z := by
  obtain ⟨hr,hr1⟩ := arcsineParameter_bounds ha ha1
  have hb := (spectralCurvature_bounds hr.le hr1 (mul_pos ha hκ) z hz).1
  have he : (1-arcsineParameter a)^2/((a*κ)*(1+arcsineParameter a)^2) = 8/κ := by
    calc
      _ = ((1-arcsineParameter a)/(1+arcsineParameter a))^2/(a*κ) := by
        rw [div_pow,div_div]
        congr 1
        ring
      _ = (Real.sqrt (8*a))^2/(a*κ) := by rw [arcsine_ratio ha.le]
      _ = 8/κ := by
        rw [Real.sq_sqrt (by positivity : 0 ≤ 8*a)]
        field_simp
  rwa [he] at hb

theorem arcsine_parameter_log_bound {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1/128) :
    -9*Real.sqrt a ≤ Real.log (arcsineParameter a) := by
  have hspos : 0 < Real.sqrt (8*a) := Real.sqrt_pos.2 (by positivity)
  have hs := Real.sq_sqrt (by positivity : 0 ≤ 8*a)
  have hsmall : Real.sqrt (8*a) ≤ 1/2 := by nlinarith
  have hlog1 := Real.log_le_sub_one_of_pos (by positivity : 0 < 1+Real.sqrt (8*a))
  have hlog2 := log_one_sub_defect hsmall
  have hprod : 0 ≤ Real.sqrt (8*a)*(1-2*Real.sqrt (8*a)) := mul_nonneg hspos.le (by linarith)
  have hsa := Real.sq_sqrt ha.le
  have hsapos := Real.sqrt_nonneg a
  have hratio : Real.sqrt (8*a) ≤ 3*Real.sqrt a := by nlinarith
  rw [arcsineParameter,Real.log_div (by linarith : 1-Real.sqrt (8*a) ≠ 0)
    (by positivity : 1+Real.sqrt (8*a) ≠ 0)]
  nlinarith only [hlog1,hlog2,hprod,hratio]

end
end StrongSilver
