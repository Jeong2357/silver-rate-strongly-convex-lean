-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.SmoothPlanarSlope
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

namespace StrongSilver
open Real Complex
noncomputable section

def polarUnit (θ : ℝ) : ℂ := ⟨Real.cos θ,Real.sin θ⟩
def polarTangent (θ : ℝ) : ℂ := ⟨-Real.sin θ,Real.cos θ⟩
def polarNormal (k θ : ℝ) : ℂ := polarUnit θ+k • polarTangent θ
def normalAngle (k θ : ℝ) : ℝ := θ+Real.arctan k

theorem polarUnit_norm (θ : ℝ) : ‖polarUnit θ‖ = 1 := by
  have hh : ‖polarUnit θ‖^2 = Real.cos θ^2+Real.sin θ^2 := by
    rw [Complex.sq_norm]
    simp only [Complex.normSq_apply,polarUnit,pow_two]
  nlinarith [Real.sin_sq_add_cos_sq θ,norm_nonneg (polarUnit θ)]

theorem polarUnit_hasDerivAt (θ : ℝ) : HasDerivAt polarUnit (polarTangent θ) θ := by
  have hh := ((Real.hasDerivAt_cos θ).ofReal_comp).add
    (((Real.hasDerivAt_sin θ).ofReal_comp).mul_const Complex.I)
  convert! hh using 1
  · funext t
    apply Complex.ext <;> simp only [polarUnit,Pi.add_apply,Complex.add_re,Complex.add_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
      mul_zero,mul_one,zero_mul,sub_zero,add_zero,zero_add]
  · apply Complex.ext <;> simp only [polarTangent,Complex.add_re,Complex.add_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
      mul_zero,mul_one,zero_mul,sub_zero,add_zero,zero_add]

theorem polarTangent_hasDerivAt (θ : ℝ) : HasDerivAt polarTangent (-polarUnit θ) θ := by
  have hh := (((Real.hasDerivAt_sin θ).neg).ofReal_comp).add
    (((Real.hasDerivAt_cos θ).ofReal_comp).mul_const Complex.I)
  convert! hh using 1
  · funext t
    apply Complex.ext <;> simp only [polarTangent,Pi.add_apply,Pi.neg_apply,Complex.add_re,Complex.add_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
      mul_zero,mul_one,zero_mul,sub_zero,add_zero,zero_add]
  · apply Complex.ext <;> simp only [polarUnit,Complex.neg_re,Complex.neg_im,Complex.add_re,Complex.add_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
      mul_zero,mul_one,zero_mul,sub_zero,add_zero,zero_add]

theorem polarUnit_inner (θ φ : ℝ) : inner ℝ (polarUnit θ) (polarUnit φ) = Real.cos (θ-φ) := by
  rw [Complex.inner]
  simp only [polarUnit,Complex.mul_re,Complex.conj_re,Complex.conj_im,Real.cos_sub]
  ring

theorem polarUnit_inner_tangent (θ φ : ℝ) : inner ℝ (polarUnit θ) (polarTangent φ) = Real.sin (θ-φ) := by
  rw [Complex.inner]
  simp only [polarUnit,polarTangent,Complex.mul_re,Complex.conj_re,Complex.conj_im,Real.sin_sub]
  ring

theorem polarNormal_angle (k θ : ℝ) :
    polarNormal k θ = Real.sqrt (1+k^2) • polarUnit (normalAngle k θ) := by
  have hs : Real.sqrt (1+k^2) ≠ 0 := (Real.sqrt_pos.2 (by positivity : 0 < 1+k^2)).ne'
  apply Complex.ext
  · simp only [polarNormal,polarUnit,polarTangent,normalAngle,Complex.add_re,Complex.smul_re,smul_eq_mul,
      Real.cos_add,Real.cos_arctan,Real.sin_arctan]
    field_simp
    <;> ring
  · simp only [polarNormal,polarUnit,polarTangent,normalAngle,Complex.add_im,Complex.smul_im,smul_eq_mul,
      Real.sin_add,Real.cos_arctan,Real.sin_arctan]
    field_simp
    <;> ring

end
end StrongSilver
