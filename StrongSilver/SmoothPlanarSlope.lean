-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PlanarDifferential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

namespace StrongSilver
open Set Real
noncomputable section

/-- A smooth replacement of min(k₀, cot(θ)/2) with the same needed bounds. -/
def smoothPlanarSlope (k₀ θ : ℝ) : ℝ := k₀*Real.cos θ/(Real.cos θ+2*k₀*Real.sin θ)
def smoothPlanarSlopeDeriv (k₀ θ : ℝ) : ℝ :=
  -2*k₀^2/(Real.cos θ+2*k₀*Real.sin θ)^2

theorem sin_add_cos_ge_one {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) (Real.pi/2)) :
    1 ≤ Real.sin θ+Real.cos θ := by
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2,Real.pi_pos])
  have hc := Real.cos_nonneg_of_mem_Icc (show θ ∈ Icc (-(Real.pi/2)) (Real.pi/2) by
    exact ⟨by linarith [hθ.1,Real.pi_pos],hθ.2⟩)
  have hid := Real.sin_sq_add_cos_sq θ
  nlinarith [mul_nonneg hs hc]

theorem smoothPlanar_denominator_lower {k₀ θ : ℝ} (hk : 0 < k₀) (hk1 : k₀ ≤ 1/2)
    (hθ : θ ∈ Icc (0 : ℝ) (Real.pi/2)) :
    2*k₀ ≤ Real.cos θ+2*k₀*Real.sin θ := by
  have hc := Real.cos_nonneg_of_mem_Icc (show θ ∈ Icc (-(Real.pi/2)) (Real.pi/2) by
    exact ⟨by linarith [hθ.1,Real.pi_pos],hθ.2⟩)
  have hs := sin_add_cos_ge_one hθ
  have hp := mul_nonneg (show 0 ≤ 1-2*k₀ by linarith) hc
  nlinarith only [mul_le_mul_of_nonneg_left hs (by linarith : 0 ≤ 2*k₀),hp]

theorem smoothPlanarSlope_bounds {k₀ θ : ℝ} (hk : 0 < k₀)
    (hθ0 : 0 ≤ θ) (hθ : θ < Real.pi/2) :
    0 < smoothPlanarSlope k₀ θ ∧ smoothPlanarSlope k₀ θ ≤ k₀ ∧
      2*smoothPlanarSlope k₀ θ*Real.sin θ ≤ Real.cos θ := by
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hθ0,Real.pi_pos],hθ⟩
  have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ0 (by linarith [Real.pi_pos])
  have hd : 0 < Real.cos θ+2*k₀*Real.sin θ := by positivity
  unfold smoothPlanarSlope
  refine ⟨div_pos (mul_pos hk hc) hd,(div_le_iff₀ hd).mpr ?_,?_⟩
  · nlinarith only [mul_nonneg (by positivity : 0 ≤ 2*k₀^2) hs]
  · rw [mul_div_assoc',div_mul_eq_mul_div]
    apply (div_le_iff₀ hd).mpr
    nlinarith only [sq_nonneg (Real.cos θ)]

theorem smoothPlanarSlope_hasDerivAt {k₀ θ : ℝ} (hd : Real.cos θ+2*k₀*Real.sin θ ≠ 0) :
    HasDerivAt (smoothPlanarSlope k₀) (smoothPlanarSlopeDeriv k₀ θ) θ := by
  have hh := ((Real.hasDerivAt_cos θ).const_mul k₀).div
    ((Real.hasDerivAt_cos θ).add ((Real.hasDerivAt_sin θ).const_mul (2*k₀))) hd
  simp only [Pi.add_apply] at hh
  convert! hh using 1
  unfold smoothPlanarSlopeDeriv
  field_simp
  nlinarith only [Real.sin_sq_add_cos_sq θ]

theorem smoothPlanarSlopeDeriv_bounds {k₀ θ : ℝ} (hk : 0 < k₀) (hk1 : k₀ ≤ 1/2)
    (hθ : θ ∈ Icc (0 : ℝ) (Real.pi/2)) :
    -(1 : ℝ)/2 ≤ smoothPlanarSlopeDeriv k₀ θ ∧ smoothPlanarSlopeDeriv k₀ θ < 0 := by
  have hd := smoothPlanar_denominator_lower hk hk1 hθ
  have hdpos : 0 < Real.cos θ+2*k₀*Real.sin θ := lt_of_lt_of_le (by linarith) hd
  have hsq : 0 < (Real.cos θ+2*k₀*Real.sin θ)^2 := sq_pos_of_pos hdpos
  have hsqbd : (2*k₀)^2 ≤ (Real.cos θ+2*k₀*Real.sin θ)^2 := by
    gcongr
  unfold smoothPlanarSlopeDeriv
  constructor
  · apply (le_div_iff₀ hsq).mpr
    nlinarith only [hsqbd]
  · exact div_neg_of_neg_of_pos (by nlinarith [sq_pos_of_pos hk]) hsq

theorem smoothPlanarSlope_inverse {k₀ θ : ℝ} (hk : k₀ ≠ 0) (hc : Real.cos θ ≠ 0)
    (hd : Real.cos θ+2*k₀*Real.sin θ ≠ 0) :
    (smoothPlanarSlope k₀ θ)⁻¹ = k₀⁻¹+2*Real.tan θ := by
  unfold smoothPlanarSlope
  rw [Real.tan_eq_sin_div_cos]
  field_simp

end
end StrongSilver
