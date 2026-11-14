-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.AttachmentSourceProperties
import StrongSilver.AttachmentRatios

namespace StrongSilver
noncomputable section
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] {ι κ τ : Type*}
set_option maxHeartbeats 1000000

theorem attachment_height (F : SupportFamily ι W) (G : SupportFamily κ V)
    (H : SupportFamily τ (AttachmentSpace V W)) {E X : W} {Y : V} {a M K : ℝ}
    (hE : E ≠ 0) (hY : Y ≠ 0) (hX : X ≠ 0) (horth : inner ℝ X E = 0)
    (ha : 0 ≤ a) (hM : 0 < M) (hK : 0 ≤ K)
    (hlinear : ∀ i, inner ℝ X (F.z i) ≤ M*F.d i+K)
    (horigin : ∀ k, AttachmentOrigin F G E Y a (H.z k) (H.g k) (H.d k)) (k : τ) :
    max (inner ℝ (alignedAttachment E Y X) (H.z k)-
      ((K+M*a)/‖X‖^2)*‖alignedAttachment E Y X‖^2) 0/M ≤ H.d k := by
  let A := alignedAttachment E Y
  let c := (‖Y‖/‖E‖)^2
  let Z := (K+M*a)/‖X‖^2
  have hc : 0 ≤ c := sq_nonneg _
  have hZ : 0 ≤ Z := div_nonneg (add_nonneg hK (mul_nonneg hM.le ha)) (sq_nonneg _)
  have hZn : Z*‖X‖^2 = K+M*a := div_mul_cancel₀ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hX))
  have hT : ∀ x y, inner ℝ (A x) (A y) = c*inner ℝ x y := alignedAttachment_inner hE hY
  have hn : ‖A X‖^2 = c*‖X‖^2 := alignedAttachment_norm_sq hE hY X
  have hunit := unitDirection_source_orthogonal horth
  have hold (z : V) : inner ℝ (A X) (retainedMap (W := W) z) = 0 :=
    attachment_source_orthogonal (unitDirection Y) (‖Y‖/‖E‖) hunit z
  apply H.positive_part_height hM
  intro j
  rcases horigin j with ⟨i,hz,hg,hd⟩ | ⟨i,hz,hg,hd⟩
  · rw [hz,hd,hT,hn]
    have hm := mul_le_mul_of_nonneg_left (hlinear i) hc
    have he := congrArg (fun t : ℝ => c*t) hZn
    nlinarith only [hm,he]
  · rw [hz,hold]
    have hnonneg := mul_nonneg hZ (sq_nonneg ‖A X‖)
    have hheight := mul_nonneg hM.le (H.nonnegative j)
    nlinarith only [hnonneg,hheight]

theorem attachment_source_slope_cap (F : SupportFamily ι W) (G : SupportFamily κ V)
    (H : SupportFamily τ (AttachmentSpace V W)) {E X : W} {Y : V} {a B : ℝ}
    (hE : E ≠ 0) (hY : Y ≠ 0) (horth : inner ℝ X E = 0) (hB : 0 ≤ B)
    (hcap : ∀ i, inner ℝ X (F.g i) ≤ B)
    (horigin : ∀ k, AttachmentOrigin F G E Y a (H.z k) (H.g k) (H.d k)) (k : τ) :
    inner ℝ (alignedAttachment E Y X) (H.g k) ≤ (‖Y‖/‖E‖)^2*B := by
  rcases horigin k with ⟨i,hz,hg,hd⟩ | ⟨i,hz,hg,hd⟩
  · rw [hg,alignedAttachment_inner hE hY]
    exact mul_le_mul_of_nonneg_left (hcap i) (sq_nonneg _)
  · rw [hg]
    have he := attachment_source_orthogonal (unitDirection Y) (‖Y‖/‖E‖)
      (unitDirection_source_orthogonal horth) (G.g i)
    change inner ℝ (attachmentMap _ _ _ X) (retainedMap (W := W) (G.g i)) ≤ _
    rw [he]
    exact mul_nonneg (sq_nonneg _) hB

end
end StrongSilver
