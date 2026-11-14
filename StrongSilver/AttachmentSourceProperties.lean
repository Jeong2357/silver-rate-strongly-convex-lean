-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.AttachmentNormalization
import StrongSilver.SupportSourceBounds

namespace StrongSilver
noncomputable section
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] {ι κ τ : Type*}
set_option maxHeartbeats 1000000

def AttachmentOrigin (F : SupportFamily ι W) (G : SupportFamily κ V) (E : W) (Y : V) (a : ℝ)
    (z g : AttachmentSpace V W) (d : ℝ) : Prop :=
  (∃ i, z = alignedAttachment E Y (F.z i) ∧ g = alignedAttachment E Y (F.g i) ∧
    d = (‖Y‖/‖E‖)^2*(F.d i-a)) ∨
  (∃ j, z = retainedMap (W := W) (G.z j) ∧ g = retainedMap (W := W) (G.g j) ∧ d = G.d j)

theorem attachment_source_properties (F : SupportFamily ι W) (G : SupportFamily κ V)
    (H : SupportFamily τ (AttachmentSpace V W)) {E X : W} {Y : V} {a B : ℝ}
    (hE : E ≠ 0) (hY : Y ≠ 0) (horth : inner ℝ X E = 0) (hpositive : F.PositiveAt X)
    (ha : 0 ≤ a) (hB : 0 < B) (hfloor : ∀ i, a ≤ F.d i) (hcap : ∀ i, inner ℝ X (F.g i) ≤ B)
    (horigin : ∀ k, AttachmentOrigin F G E Y a (H.z k) (H.g k) (H.d k)) :
    H.PositiveAt (alignedAttachment E Y X) ∧ H.Gate (alignedAttachment E Y X) (a/B) := by
  let A := alignedAttachment E Y
  let c := (‖Y‖/‖E‖)^2
  have hc : 0 ≤ c := sq_nonneg _
  have hT : ∀ x y, inner ℝ (A x) (A y) = c*inner ℝ x y := alignedAttachment_inner hE hY
  have hunit := unitDirection_source_orthogonal horth
  have hold (z : V) : inner ℝ (A X) (retainedMap (W := W) z) = 0 :=
    attachment_source_orthogonal (unitDirection Y) (‖Y‖/‖E‖) hunit z
  have hlocalgate := (F.shifted a ha hfloor).transport_gate A c hc hT (F.shifted_gate ha hB hfloor hcap)
  have holdgate := G.retained_gate_at_orthogonal (unitDirection E) (unitDirection Y) (‖Y‖/‖E‖) (a/B) hunit
  refine ⟨⟨fun k => ?_,fun k => ?_⟩,fun k => ?_⟩
  · rcases horigin k with ⟨i,hz,hg,hd⟩ | ⟨j,hz,hg,hd⟩
    · rw [hz,hT]
      exact mul_nonneg hc (hpositive.1 i)
    · rw [hz,hold]
  · rcases horigin k with ⟨i,hz,hg,hd⟩ | ⟨j,hz,hg,hd⟩
    · rw [hg,hT]
      exact mul_nonneg hc (hpositive.2 i)
    · rw [hg,hold]
  · rcases horigin k with ⟨i,hz,hg,hd⟩ | ⟨j,hz,hg,hd⟩
    · rw [hz,hg,hd]
      exact hlocalgate i
    · rw [hz,hg,hd]
      simpa only [SupportFamily.retained,SupportFamily.transport,alignedAttachment,one_mul] using holdgate j

end
end StrongSilver
