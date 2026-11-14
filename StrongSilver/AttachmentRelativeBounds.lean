-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.AttachmentSourceProperties
import StrongSilver.AttachmentRatios
import StrongSilver.PlaneProjectionBounds

namespace StrongSilver
noncomputable section
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] {ι κ τ : Type*}
set_option maxHeartbeats 1200000

theorem alignedAttachment_norm {E : W} {Y : V} (hE : E ≠ 0) (hY : Y ≠ 0) (z : W) :
    ‖alignedAttachment E Y z‖ = (‖Y‖/‖E‖)*‖z‖ := by
  have hh := alignedAttachment_norm_sq hE hY z
  have hpos : 0 ≤ (‖Y‖/‖E‖)*‖z‖ := mul_nonneg (div_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
  nlinarith only [hh,norm_nonneg (alignedAttachment E Y z),hpos]

theorem aligned_relative_projection {E X z : W} {Y : V} {B : ℝ}
    (hE : E ≠ 0) (hY : Y ≠ 0) (hX : X ≠ 0) (hz : ‖z‖ ≤ B*‖X‖) :
    |inner ℝ (unitDirection (alignedAttachment E Y X)) (alignedAttachment E Y z)| ≤
      B*‖alignedAttachment E Y X‖ := by
  have hh := unitDirection_projection_le (alignedAttachment_ne_zero hE hY hX) (alignedAttachment E Y z)
  rw [alignedAttachment_norm hE hY]
  have hs := mul_le_mul_of_nonneg_left hz (div_nonneg (norm_nonneg Y) (norm_nonneg E))
  rw [alignedAttachment_norm hE hY] at hh
  nlinarith only [hh,hs]

theorem aligned_retained_source_orthogonal {E X : W} {Y : V}
    (horth : inner ℝ X E = 0) (z : V) :
    inner ℝ (unitDirection (alignedAttachment E Y X)) (retainedMap (W := W) z) = 0 := by
  have hh := attachment_source_orthogonal (unitDirection Y) (‖Y‖/‖E‖)
    (unitDirection_source_orthogonal horth) z
  change inner ℝ (alignedAttachment E Y X) (retainedMap (W := W) z) = 0 at hh
  rw [unitDirection,real_inner_smul_left]
  change ‖alignedAttachment E Y X‖⁻¹*inner ℝ (alignedAttachment E Y X) (retainedMap (W := W) z) = 0
  rw [hh,mul_zero]

theorem attachment_relative_bounds (F : SupportFamily ι W) (G : SupportFamily κ V)
    (J : SupportFamily τ (AttachmentSpace V W)) {E X : W} {Y : V} {d B : ℝ}
    (hE : E ≠ 0) (hY : Y ≠ 0) (hX : X ≠ 0) (horth : inner ℝ X E = 0) (hB : 0 ≤ B)
    (hlocal : ∀ i, ‖F.z i‖ ≤ B*‖X‖ ∧ ‖F.g i‖ ≤ B*‖X‖)
    (horigin : ∀ k, AttachmentOrigin F G E Y d (J.z k) (J.g k) (J.d k)) (k : τ) :
    |inner ℝ (unitDirection (alignedAttachment E Y X)) (J.z k)| ≤ B*‖alignedAttachment E Y X‖ ∧
    |inner ℝ (unitDirection (alignedAttachment E Y X)) (J.g k)| ≤ B*‖alignedAttachment E Y X‖ := by
  rcases horigin k with ⟨i,hz,hg,hd⟩ | ⟨j,hz,hg,hd⟩
  · rw [hz,hg]
    exact ⟨aligned_relative_projection hE hY hX (hlocal i).1,aligned_relative_projection hE hY hX (hlocal i).2⟩
  · rw [hz,hg,aligned_retained_source_orthogonal horth,aligned_retained_source_orthogonal horth,abs_zero]
    exact ⟨mul_nonneg hB (norm_nonneg _),mul_nonneg hB (norm_nonneg _)⟩

theorem attachment_relative_bounds_pair (F : SupportFamily ι W) (G : SupportFamily κ V)
    (J : SupportFamily τ (AttachmentSpace V W)) {E X : W} {Y : V} {d Bz Bg : ℝ}
    (hE : E ≠ 0) (hY : Y ≠ 0) (hX : X ≠ 0) (horth : inner ℝ X E = 0) (hBz : 0 ≤ Bz) (hBg : 0 ≤ Bg)
    (hlocal : ∀ i, ‖F.z i‖ ≤ Bz*‖X‖ ∧ ‖F.g i‖ ≤ Bg*‖X‖)
    (horigin : ∀ k, AttachmentOrigin F G E Y d (J.z k) (J.g k) (J.d k)) (k : τ) :
    |inner ℝ (unitDirection (alignedAttachment E Y X)) (J.z k)| ≤ Bz*‖alignedAttachment E Y X‖ ∧
    |inner ℝ (unitDirection (alignedAttachment E Y X)) (J.g k)| ≤ Bg*‖alignedAttachment E Y X‖ := by
  rcases horigin k with ⟨i,hz,hg,hd⟩ | ⟨j,hz,hg,hd⟩
  · rw [hz,hg]
    exact ⟨aligned_relative_projection hE hY hX (hlocal i).1,aligned_relative_projection hE hY hX (hlocal i).2⟩
  · rw [hz,hg,aligned_retained_source_orthogonal horth,aligned_retained_source_orthogonal horth,abs_zero]
    exact ⟨mul_nonneg hBz (norm_nonneg _),mul_nonneg hBg (norm_nonneg _)⟩

end
end StrongSilver
