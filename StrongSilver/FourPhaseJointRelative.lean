-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseAttachedRatio
import StrongSilver.SupportFamilies
import StrongSilver.UnitProjectionBound

namespace StrongSilver.FourPhase
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {ι κ : Type*}
set_option maxHeartbeats 2000000

/-- Relative source caps are unchanged by spatial scaling; all retained
contacts have zero source projection. -/
theorem joint_source_caps {L : SupportFamily κ Coordinates} {G : SupportFamily ι V}
    {F : SupportFamily (κ ⊕ ι) (AttachmentSpace V Coordinates)} {X : Coordinates} {Y : V} {K M B : ℝ}
    (hY : Y ≠ 0) (hX : inner ℝ X axis = 0) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hlocal : ∀ j, |inner ℝ X (L.z j)| ≤ M*‖X‖^2 ∧ |inner ℝ X (L.g j)| ≤ B*‖X‖^2)
    (hnew : ∀ j, F.z (Sum.inl j) = axisAttachment Y K (L.z j) ∧ F.g (Sum.inl j) = axisAttachment Y K (L.g j))
    (hold : ∀ j, F.z (Sum.inr j) = retainedMap (W := Coordinates) (G.z j) ∧
      F.g (Sum.inr j) = retainedMap (W := Coordinates) (G.g j)) (i : κ ⊕ ι) :
    |inner ℝ (axisAttachment Y K X) (F.z i)| ≤ M*‖axisAttachment Y K X‖^2 ∧
    |inner ℝ (axisAttachment Y K X) (F.g i)| ≤ B*‖axisAttachment Y K X‖^2 := by
  have hc : 0 ≤ (‖Y‖/K)^2 := sq_nonneg _
  cases i with
  | inl j =>
    rw [(hnew j).1,(hnew j).2,axisAttachment_inner hY,axisAttachment_inner hY,
      abs_mul,abs_mul,abs_of_nonneg hc,axisAttachment_norm_sq hY]
    have hz := mul_le_mul_of_nonneg_left (hlocal j).1 hc
    have hg := mul_le_mul_of_nonneg_left (hlocal j).2 hc
    constructor <;> nlinarith only [hz,hg]
  | inr j =>
    rw [(hold j).1,(hold j).2,axisAttachment_orthogonal hX,axisAttachment_orthogonal hX,abs_zero]
    exact ⟨mul_nonneg hM (sq_nonneg _),mul_nonneg hB (sq_nonneg _)⟩

theorem unit_relative_of_quadratic {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {X z g : W} {M B : ℝ} (hX : X ≠ 0)
    (hz : |inner ℝ X z| ≤ M*‖X‖^2) (hg : |inner ℝ X g| ≤ B*‖X‖^2) :
    |inner ℝ (unitDirection X) z| ≤ M*‖X‖ ∧ |inner ℝ (unitDirection X) g| ≤ B*‖X‖ := by
  constructor
  · apply unit_projection_of_inner_bound hX
    nlinarith only [hz]
  · apply unit_projection_of_inner_bound hX
    nlinarith only [hg]

end
end StrongSilver.FourPhase
