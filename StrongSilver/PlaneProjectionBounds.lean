-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PlaneAttachmentSupport
import StrongSilver.AttachmentNormalization

namespace StrongSilver
open Real Complex
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
set_option maxHeartbeats 1000000

theorem plane_attachment_norm {f : V} (hf : inner ℝ f f = 1) (z : ℂ) :
    ‖attachmentMap Complex.I f 1 z‖ = ‖z‖ := by
  have hh := attachment_norm_sq complex_I_inner_self hf 1 z
  simp only [one_pow,one_mul] at hh
  nlinarith only [hh,norm_nonneg z,norm_nonneg (attachmentMap Complex.I f 1 z)]

theorem plane_attachment_ne_zero {f : V} (hf : inner ℝ f f = 1) {z : ℂ} (hz : z ≠ 0) :
    attachmentMap Complex.I f 1 z ≠ 0 := by
  intro hh
  have he := plane_attachment_norm hf z
  rw [hh,norm_zero] at he
  exact hz (norm_eq_zero.mp he.symm)

theorem norm_unitDirection {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {x : W} (hx : x ≠ 0) : ‖unitDirection x‖ = 1 := by
  have hh := unitDirection_inner hx
  rw [real_inner_self_eq_norm_sq] at hh
  nlinarith only [hh,norm_nonneg (unitDirection x)]

theorem unitDirection_projection_le {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {x : W} (hx : x ≠ 0) (z : W) : |inner ℝ (unitDirection x) z| ≤ ‖z‖ := by
  have hh := abs_real_inner_le_norm (unitDirection x) z
  simpa only [norm_unitDirection hx,one_mul] using hh

theorem plane_local_projection {f : V} (hf : inner ℝ f f = 1) {x : ℂ} (hx : x ≠ 0) (z : ℂ) :
    |inner ℝ (unitDirection (attachmentMap Complex.I f 1 x)) (attachmentMap Complex.I f 1 z)| ≤ ‖z‖ := by
  have hh := unitDirection_projection_le (plane_attachment_ne_zero hf hx) (attachmentMap Complex.I f 1 z)
  rwa [plane_attachment_norm hf] at hh

theorem plane_retained_projection {f : V} (hf : inner ℝ f f = 1) {x : ℂ} (hx : x ≠ 0) (z : V) :
    |inner ℝ (unitDirection (attachmentMap Complex.I f 1 x)) (retainedMap (W := ℂ) z)| ≤ |inner ℝ f z| := by
  rw [unitDirection,real_inner_smul_left,plane_attachment_norm hf,plane_attachment_cross,
    complex_inner_coordinates,mul_zero,zero_add,abs_mul,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)),abs_mul]
  have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hh := mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm x) (inv_nonneg.mpr hnorm.le)
  rw [inv_mul_cancel₀ hnorm.ne'] at hh
  have hfinal := mul_le_mul_of_nonneg_right hh (abs_nonneg (inner ℝ f z))
  simpa only [mul_assoc,one_mul] using hfinal

end
end StrongSilver
