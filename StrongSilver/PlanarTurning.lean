-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PlanarBoundaryCurve

namespace StrongSilver
open Real Set Complex
noncomputable section

def planarDet (x y : ℂ) : ℝ := x.re*y.im-x.im*y.re

theorem planarDet_add_right (x y z : ℂ) : planarDet x (y+z) = planarDet x y+planarDet x z := by
  simp only [planarDet,Complex.add_re,Complex.add_im]
  ring

theorem planarDet_smul_right (x y : ℂ) (a : ℝ) : planarDet x (a • y) = a*planarDet x y := by
  simp only [planarDet,Complex.smul_re,Complex.smul_im,smul_eq_mul]
  ring

@[simp] theorem planarDet_self (x : ℂ) : planarDet x x = 0 := by unfold planarDet; ring

theorem planarDet_frame (a b c d θ : ℝ) :
    planarDet (a • polarUnit θ+b • polarTangent θ) (c • polarUnit θ+d • polarTangent θ) = a*d-b*c := by
  simp only [planarDet,polarUnit,polarTangent,Complex.add_re,Complex.add_im,Complex.smul_re,Complex.smul_im,smul_eq_mul]
  linear_combination (a*d-b*c)*(Real.sin_sq_add_cos_sq θ)

theorem planarBoundaryField_eq_normal {μ : ℝ} {r k J : ℝ → ℝ} {θ : ℝ} (hk : k θ ≠ 0) :
    planarBoundaryField μ r k J θ = polarArc r θ+(μ*(J θ/k θ)) • polarNormal (k θ) θ := by
  have he : (J θ/k θ)*k θ = J θ := div_mul_cancel₀ _ hk
  unfold planarBoundaryField polarArc polarNormal
  simp only [smul_add,smul_smul]
  have hm : μ*(J θ/k θ)*k θ = μ*J θ := by rw [mul_assoc,he]
  simp only [hm]
  module

theorem planarBoundaryField_coordinates {μ : ℝ} {r k J : ℝ → ℝ} {θ : ℝ}
    (hμ : 0 ≤ μ) (hr : 0 < r θ) (hk : 0 < k θ) (hJ : 0 ≤ J θ)
    (hθ0 : 0 ≤ θ) (hθ : θ < Real.pi/2) (htransverse : 2*k θ*Real.sin θ ≤ Real.cos θ) :
    0 < (planarBoundaryField μ r k J θ).re ∧ 0 ≤ (planarBoundaryField μ r k J θ).im := by
  obtain ⟨hnx,hny⟩ := polarNormal_coordinates hk.le hθ0 hθ htransverse
  have hcos := Real.cos_pos_of_mem_Ioo (show θ ∈ Ioo (-(Real.pi/2)) (Real.pi/2) by
    exact ⟨by linarith [Real.pi_pos],hθ⟩)
  have hsin := Real.sin_nonneg_of_nonneg_of_le_pi hθ0 (by linarith [Real.pi_pos])
  have hcoef : 0 ≤ μ*(J θ/k θ) := mul_nonneg hμ (div_nonneg hJ hk.le)
  rw [planarBoundaryField_eq_normal hk.ne']
  simp only [polarArc,polarUnit,Complex.add_re,Complex.add_im,Complex.smul_re,Complex.smul_im,smul_eq_mul]
  constructor
  · exact add_pos_of_pos_of_nonneg (mul_pos hr hcos) (mul_nonneg hcoef hnx.le)
  · exact add_nonneg (mul_nonneg hr.le hsin) (mul_nonneg hcoef hny)

theorem planarBoundaryField_eq_affine {μ : ℝ} {r k J : ℝ → ℝ} (θ : ℝ) :
    planarBoundaryField μ r k J θ = μ • planarBoundaryCurve r k J θ+(1-μ) • polarArc r θ := by
  unfold planarBoundaryField planarBoundaryCurve polarArc
  module

theorem planarBoundaryField_hasDerivWithinAt {μ t θ : ℝ} {r k J : ℝ → ℝ} {S : Set ℝ}
    (hcurve : HasDerivWithinAt (planarBoundaryCurve r k J) (t • planarBoundaryField μ r k J θ) S θ)
    (hr : HasDerivWithinAt r (-k θ*r θ) S θ) :
    HasDerivWithinAt (planarBoundaryField μ r k J)
      ((μ*t) • planarBoundaryField μ r k J θ+((1-μ)*r θ) • rotatedPolarNormal (k θ) θ) S θ := by
  have harc : HasDerivWithinAt (polarArc r) (r θ • rotatedPolarNormal (k θ) θ) S θ := by
    have hh := hr.smul (polarUnit_hasDerivAt θ).hasDerivWithinAt
    convert! hh using 1
    unfold rotatedPolarNormal
    module
  have hh := (hcurve.const_smul μ).add (harc.const_smul (1-μ))
  have he : planarBoundaryField μ r k J =
      (fun s => μ • planarBoundaryCurve r k J s+(1-μ) • polarArc r s) := by
    funext s
    exact planarBoundaryField_eq_affine s
  rw [he]
  rw [he] at hh
  convert! hh using 1
  module

/-- The physical field turns strictly counterclockwise along the boundary. -/
theorem planarBoundaryField_turning_pos {μ t θ : ℝ} {r k J : ℝ → ℝ}
    (hμ : 0 ≤ μ) (hμ1 : μ < 1) (hr : 0 < r θ) (hk : 0 < k θ) (hJ : 0 ≤ J θ) :
    0 < planarDet (planarBoundaryField μ r k J θ)
      ((μ*t) • planarBoundaryField μ r k J θ+((1-μ)*r θ) • rotatedPolarNormal (k θ) θ) := by
  rw [planarDet_add_right,planarDet_smul_right,planarDet_self,mul_zero,zero_add,planarDet_smul_right]
  unfold planarBoundaryField rotatedPolarNormal
  have hdet := planarDet_frame (r θ+μ*J θ/k θ) (μ*J θ) (-k θ) 1 θ
  simp only [one_smul] at hdet
  rw [hdet]
  have hpos : 0 < (r θ+μ*J θ/k θ)*1-μ*J θ*(-k θ) := by
    have hd := div_nonneg (mul_nonneg hμ hJ) hk.le
    have hp := mul_nonneg (mul_nonneg hμ hJ) hk.le
    nlinarith only [hr,hd,hp]
  exact mul_pos (mul_pos (sub_pos.mpr hμ1) hr) hpos

end
end StrongSilver
