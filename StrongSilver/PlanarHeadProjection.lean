-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PlanarBodyGeometry

namespace StrongSilver.PlanarBoundaryCertificate
open Set Real Complex
noncomputable section
variable {A μ : ℝ} (C : PlanarBoundaryCertificate A μ)
include C
set_option maxHeartbeats 1000000

theorem slope_zero : planarSlope A 0 = planarSlopeScale A := by
  simp only [planarSlope,smoothPlanarSlope,Real.cos_zero,Real.sin_zero,mul_one,mul_zero,add_zero,div_one]

theorem head_arc_eq : polarArc (planarRadius A) 0 = (⟨planarRadius A 0,0⟩ : ℂ) := by
  apply Complex.ext <;> simp only [polarArc,polarUnit,Real.cos_zero,Real.sin_zero,
    Complex.smul_re,Complex.smul_im,smul_eq_mul,mul_one,mul_zero]

theorem head_normal_eq : polarNormal (planarSlope A 0) 0 = (⟨1,planarSlopeScale A⟩ : ℂ) := by
  apply Complex.ext <;> simp only [polarNormal,polarUnit,polarTangent,C.slope_zero,Real.cos_zero,Real.sin_zero,
    Complex.add_re,Complex.add_im,Complex.smul_re,Complex.smul_im,smul_eq_mul,neg_zero,mul_zero,mul_one,add_zero,zero_add]

theorem body_head_normal {v : ℂ} (hv : v ∈ C.body.carrier) :
    inner ℝ (⟨1,planarSlopeScale A⟩ : ℂ) (v-(⟨planarRadius A 0,0⟩ : ℂ)) ≤ 0 := by
  have hh := radialArcBody_normal C.radius_continuousOn
    (show (0 : ℝ) ∈ Icc (0 : ℝ) (planarTerminalAngle A) from ⟨le_rfl,C.angle_pos.le⟩)
    (C.radius_pos 0).le (C.arc_support ⟨le_rfl,C.angle_pos.le⟩) v hv
  rwa [C.head_arc_eq,C.head_normal_eq] at hh

theorem projection_head_region {x y : ℝ} (hx : planarRadius A 0 ≤ x) (hy : 0 ≤ y)
    (hyu : y ≤ planarSlopeScale A*(x-planarRadius A 0)) :
    C.body.projection (⟨x,y⟩ : ℂ) = (⟨planarRadius A 0,0⟩ : ℂ) := by
  have hratio : y/planarSlopeScale A ≤ x-planarRadius A 0 :=
    (div_le_iff₀ C.scale_pos).mpr (by nlinarith only [hyu])
  have ha : 0 ≤ x-planarRadius A 0-y/planarSlopeScale A := sub_nonneg.mpr hratio
  have hb : 0 ≤ y/planarSlopeScale A := div_nonneg hy C.scale_pos.le
  apply C.body.projection_eq_of_normal _ _ C.body_head_mem
  intro v hv
  have he : (⟨x,y⟩ : ℂ)-(⟨planarRadius A 0,0⟩ : ℂ) =
      (x-planarRadius A 0-y/planarSlopeScale A) • (⟨1,0⟩ : ℂ)+
        (y/planarSlopeScale A) • (⟨1,planarSlopeScale A⟩ : ℂ) := by
    apply Complex.ext <;>
      simp only [Complex.sub_re,Complex.sub_im,Complex.add_re,Complex.add_im,Complex.smul_re,Complex.smul_im,
        smul_eq_mul,mul_one,mul_zero,zero_add,add_zero,sub_zero]
    · ring
    · exact (div_mul_cancel₀ y C.scale_pos.ne').symm
  rw [he,inner_add_left,real_inner_smul_left,real_inner_smul_left]
  have hxnormal : inner ℝ (⟨1,0⟩ : ℂ) (v-(⟨planarRadius A 0,0⟩ : ℂ)) ≤ 0 := by
    simpa only [complex_inner_coordinates,Complex.sub_re,Complex.sub_im,one_mul,zero_mul,add_zero] using
      sub_nonpos.mpr (C.body_re_upper hv)
  exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha hxnormal)
    (mul_nonpos_of_nonneg_of_nonpos hb (C.body_head_normal hv))

theorem axis_gradient_im {x : ℝ} (hx : 0 ≤ x) :
    (stronglyConvexGradient μ (Moreau.gradient C.body.supportEpigraph) (⟨x,0⟩ : ℂ)).im = 0 := by
  by_cases hxu : x ≤ planarRadius A 0
  · have hh := support_gradient_at_body_point (C.body_axis_mem hx hxu) μ
    exact congrArg Complex.im hh
  · have hxp : planarRadius A 0 ≤ x := le_of_not_ge hxu
    have hp := C.projection_head_region hxp (le_refl (0 : ℝ))
      (mul_nonneg C.scale_pos.le (sub_nonneg.mpr hxp))
    unfold stronglyConvexGradient
    rw [C.body.support_envelope_gradient,hp]
    simp only [Complex.add_im,Complex.smul_im,smul_eq_mul,mul_zero,add_zero]

theorem physical_gradient_zero : stronglyConvexGradient μ (Moreau.gradient C.body.supportEpigraph) 0 = 0 :=
  support_gradient_at_body_point C.body.zero_mem μ

end
end StrongSilver.PlanarBoundaryCertificate
