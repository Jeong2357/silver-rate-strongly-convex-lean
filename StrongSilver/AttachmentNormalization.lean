-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.OrthogonalAttachment

namespace StrongSilver
noncomputable section
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
set_option maxHeartbeats 1000000

def unitDirection (x : V) : V := ‖x‖⁻¹ • x

theorem unitDirection_inner {x : V} (hx : x ≠ 0) : inner ℝ (unitDirection x) (unitDirection x) = 1 := by
  rw [unitDirection,real_inner_smul_left,real_inner_smul_right,real_inner_self_eq_norm_sq]
  field_simp [(norm_ne_zero_iff.mpr hx)]

theorem norm_smul_unitDirection {x : V} (hx : x ≠ 0) : ‖x‖ • unitDirection x = x := by
  rw [unitDirection,smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx),one_smul]

def alignedAttachment (E : W) (Y : V) : W →ₗ[ℝ] AttachmentSpace V W :=
  attachmentMap (unitDirection E) (unitDirection Y) (‖Y‖/‖E‖)

theorem alignedAttachment_endpoint {E : W} {Y : V} (hE : E ≠ 0) (hY : Y ≠ 0) :
    alignedAttachment E Y E = retainedMap (W := W) Y := by
  have he := attachment_endpoint (unitDirection_inner hE) (unitDirection Y) (‖Y‖/‖E‖) ‖E‖
  rw [norm_smul_unitDirection hE,div_mul_cancel₀ ‖Y‖ (norm_ne_zero_iff.mpr hE),norm_smul_unitDirection hY] at he
  exact he

theorem alignedAttachment_inner {E : W} {Y : V} (hE : E ≠ 0) (hY : Y ≠ 0) (x z : W) :
    inner ℝ (alignedAttachment E Y x) (alignedAttachment E Y z) =
      (‖Y‖/‖E‖)^2*inner ℝ x z :=
  attachment_inner (unitDirection_inner hE) (unitDirection_inner hY) _ _ _

theorem unitDirection_inner_nonpositive {E x : W} (hx : inner ℝ E x ≤ 0) :
    inner ℝ (unitDirection E) x ≤ 0 := by
  rw [unitDirection,real_inner_smul_left]
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (norm_nonneg E)) hx

theorem unitDirection_inner_nonnegative {Y z : V} (hz : 0 ≤ inner ℝ Y z) :
    0 ≤ inner ℝ (unitDirection Y) z := by
  rw [unitDirection,real_inner_smul_left]
  exact mul_nonneg (inv_nonneg.mpr (norm_nonneg Y)) hz

theorem alignedAttachment_projection_bound {E z : W} {Y : V} {η : ℝ} (hE : E ≠ 0)
    (hproj : inner ℝ E z ≤ η*‖E‖^2) :
    (‖Y‖/‖E‖)*inner ℝ (unitDirection E) z ≤ η*‖Y‖ := by
  rw [unitDirection,real_inner_smul_left]
  have hp := mul_le_mul_of_nonneg_left hproj (div_nonneg (norm_nonneg Y) (sq_nonneg ‖E‖))
  have hEn := norm_ne_zero_iff.mpr hE
  have hl : (‖Y‖/‖E‖^2)*inner ℝ E z = (‖Y‖/‖E‖)*(‖E‖⁻¹*inner ℝ E z) := by ring
  have hr : (‖Y‖/‖E‖^2)*(η*‖E‖^2) = η*‖Y‖ := by field_simp [hEn] <;> ring
  rwa [hl,hr] at hp

theorem unitDirection_source_orthogonal {E X : W} (hX : inner ℝ X E = 0) :
    inner ℝ (unitDirection E) X = 0 := by
  rw [unitDirection,real_inner_smul_left,real_inner_comm X E,hX,mul_zero]

end
end StrongSilver
