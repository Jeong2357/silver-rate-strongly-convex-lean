-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ArcBodyBounds

namespace StrongSilver
open Real Set Complex
noncomputable section

theorem terminal_polar_vector {ε : ℝ} (hε : 0 < ε) :
    Real.sqrt (1+ε^2) • polarUnit (Real.arctan ε⁻¹) = (⟨ε,1⟩ : ℂ) := by
  have hsq : Real.sqrt (1+ε^2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
  rw [Real.arctan_inv_of_pos hε]
  apply Complex.ext
  · simp only [polarUnit,Complex.smul_re,smul_eq_mul,Real.cos_pi_div_two_sub,Real.sin_arctan]
    field_simp
  · simp only [polarUnit,Complex.smul_im,smul_eq_mul,Real.sin_pi_div_two_sub,Real.cos_arctan]
    field_simp

theorem smoothPlanarSlope_terminal {k₀ ε : ℝ} (hε : 0 < ε) :
    smoothPlanarSlope k₀ (Real.arctan ε⁻¹) = k₀*ε/(ε+2*k₀) := by
  have hsq : Real.sqrt (1+ε^2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
  rw [Real.arctan_inv_of_pos hε]
  unfold smoothPlanarSlope
  rw [Real.cos_pi_div_two_sub,Real.sin_pi_div_two_sub,Real.sin_arctan,Real.cos_arctan]
  field_simp

theorem smoothPlanarSlope_terminal_bounds {k₀ ε : ℝ} (hk : 0 < k₀) (hε : 0 < ε) (hεk : ε ≤ k₀) :
    ε/3 ≤ smoothPlanarSlope k₀ (Real.arctan ε⁻¹) ∧ smoothPlanarSlope k₀ (Real.arctan ε⁻¹) ≤ ε/2 := by
  rw [smoothPlanarSlope_terminal hε]
  have hd : 0 < ε+2*k₀ := by positivity
  constructor
  · apply (le_div_iff₀ hd).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hεk hε.le]
  · apply (div_le_iff₀ hd).mpr
    nlinarith only [sq_nonneg ε]

theorem CompactConvexBody.projection_self {K : CompactConvexBody ℂ} {x : ℂ} (hx : x ∈ K.carrier) :
    K.projection x = x := by
  apply K.projection_eq_of_normal x x hx
  intro w hw
  rw [sub_self,inner_zero_left]

theorem support_gradient_at_body_point {K : CompactConvexBody ℂ} {x : ℂ} (hx : x ∈ K.carrier) (μ : ℝ) :
    stronglyConvexGradient μ (Moreau.gradient K.supportEpigraph) x = x := by
  rw [stronglyConvexGradient,K.support_envelope_gradient,K.projection_self hx]
  module

theorem selected_step_at_body_point {K : CompactConvexBody ℂ} {x : ℂ} (hx : x ∈ K.carrier) (μ b : ℝ) :
    x-b • stronglyConvexGradient μ (Moreau.gradient K.supportEpigraph) x = -(b-1) • x := by
  rw [support_gradient_at_body_point hx]
  module

theorem polarNormal_coordinates {k θ : ℝ} (hk : 0 ≤ k) (hθ0 : 0 ≤ θ) (hθ : θ < Real.pi/2)
    (htransverse : 2*k*Real.sin θ ≤ Real.cos θ) :
    0 < (polarNormal k θ).re ∧ 0 ≤ (polarNormal k θ).im := by
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],hθ⟩
  have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ0 (by linarith [Real.pi_pos])
  simp only [polarNormal,polarUnit,polarTangent,Complex.add_re,Complex.add_im,Complex.smul_re,Complex.smul_im,smul_eq_mul]
  constructor
  · nlinarith only [htransverse,hc]
  · exact add_nonneg hs (mul_nonneg hk hc.le)

end
end StrongSilver
