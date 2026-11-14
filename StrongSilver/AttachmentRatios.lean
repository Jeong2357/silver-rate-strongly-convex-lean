-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.AttachmentNormalization

namespace StrongSilver
noncomputable section
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]

theorem alignedAttachment_norm_sq {E : W} {Y : V} (hE : E ≠ 0) (hY : Y ≠ 0) (X : W) :
    ‖alignedAttachment E Y X‖^2 = (‖Y‖/‖E‖)^2*‖X‖^2 := by
  rw [← real_inner_self_eq_norm_sq,alignedAttachment_inner hE hY,real_inner_self_eq_norm_sq]

theorem alignedAttachment_ne_zero {E X : W} {Y : V} (hE : E ≠ 0) (hY : Y ≠ 0) (hX : X ≠ 0) :
    alignedAttachment E Y X ≠ 0 := by
  intro hz
  have hh := alignedAttachment_norm_sq hE hY X
  rw [hz,norm_zero,zero_pow (by decide : 2 ≠ 0)] at hh
  have hp : 0 < (‖Y‖/‖E‖)^2*‖X‖^2 :=
    mul_pos (sq_pos_of_pos (div_pos (norm_pos_iff.mpr hY) (norm_pos_iff.mpr hE))) (sq_pos_of_pos (norm_pos_iff.mpr hX))
  linarith

/-- Squared norm ratios multiply exactly under normalized attachment. -/
theorem attachment_ratio {E X : W} {Y : V} (hE : E ≠ 0) (hY : Y ≠ 0) (Z : V) :
    ‖retainedMap (W := W) Z‖^2/‖alignedAttachment E Y X‖^2 =
      (‖Z‖^2/‖Y‖^2)*(‖E‖^2/‖X‖^2) := by
  have hn : ‖retainedMap (W := W) Z‖ = ‖Z‖ := retainedIsometry.norm_map Z
  rw [hn,alignedAttachment_norm_sq hE hY]
  simp only [div_eq_mul_inv,mul_inv_rev,inv_pow,div_pow,inv_inv]
  ring_nf
  simp only [inv_inv]
  ring

end
end StrongSilver
