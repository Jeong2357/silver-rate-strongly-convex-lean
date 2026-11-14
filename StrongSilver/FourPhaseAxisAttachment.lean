-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseCoordinates
import StrongSilver.AttachmentNormalization

namespace StrongSilver.FourPhase
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
set_option maxHeartbeats 2400000

def axisAttachment (Y : V) (K : ℝ) : Coordinates →ₗ[ℝ] AttachmentSpace V Coordinates :=
  attachmentMap axis (unitDirection Y) (‖Y‖/K)

theorem axisAttachment_inner {Y : V} (hY : Y ≠ 0) (K : ℝ) (z g : Coordinates) :
    inner ℝ (axisAttachment Y K z) (axisAttachment Y K g) = (‖Y‖/K)^2*inner ℝ z g :=
  attachment_inner axis_unit (unitDirection_inner hY) _ _ _

theorem axisAttachment_endpoint {Y : V} (hY : Y ≠ 0) {K : ℝ} (hK : K ≠ 0) :
    axisAttachment Y K (K • axis) = retainedMap (W := Coordinates) Y := by
  rw [axisAttachment,attachment_endpoint axis_unit,div_mul_cancel₀ _ hK,norm_smul_unitDirection hY]

theorem axisAttachment_orthogonal {Y : V} {K : ℝ} {X : Coordinates}
    (hX : inner ℝ X axis = 0) (y : V) :
    inner ℝ (axisAttachment Y K X) (retainedMap (W := Coordinates) y) = 0 := by
  apply attachment_source_orthogonal
  rw [real_inner_comm X axis,hX]

/-- Exact cancellation of the local contact value after spatial rescaling. -/
theorem axisAttachment_plane_value {Y : V} (hY : Y ≠ 0) {K b δ : ℝ} (hK : K ≠ 0)
    (z g : Coordinates) (y : V) (hb : inner ℝ axis g = b) :
    (‖Y‖/K)^2*(inner ℝ g z-δ)+
      inner ℝ (axisAttachment Y K g) (retainedMap (W := Coordinates) y-axisAttachment Y K z) =
      b*inner ℝ Y y/K-‖Y‖^2*δ/K^2 := by
  rw [inner_sub_right,axisAttachment_inner hY]
  change (‖Y‖/K)^2*(inner ℝ g z-δ)+
    ((inner ℝ (attachmentMap axis (unitDirection Y) (‖Y‖/K) g) (retainedMap y))-
      (‖Y‖/K)^2*inner ℝ g z) = _
  rw [attachment_retained_inner,hb,unitDirection,real_inner_smul_left]
  have hn := norm_ne_zero_iff.mpr hY
  field_simp
  <;> ring

end
end StrongSilver.FourPhase
