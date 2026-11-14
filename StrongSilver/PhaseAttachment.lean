-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.LocalPhaseEstimates
import StrongSilver.AttachedSupportedPath
import StrongSilver.AttachmentHeight
import StrongSilver.SupportedPathError

namespace StrongSilver.LocalPhaseCertificate
open Set Real
noncomputable section
variable {A μ b T e : ℝ} {h : List ℝ} (L : LocalPhaseCertificate A μ b T e h)
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [ProperSpace (AttachmentSpace V PhaseSpace)]
set_option maxHeartbeats 1000000

/-- The exact phase attachment of Lemma 3.5, including gate, source positivity,
positive-part height, and the squared norm ratio. -/
theorem exists_phase_attachment {m : ℕ} (Q : SupportedPath V μ m) (hY : Q.x 0 ≠ 0) {d η : ℝ}
    (hd : 0 ≤ d) (hdheight : d ≤ ((1/T-μ)/32)*Real.exp (-2*negativeLogSum h T)*e^2)
    (hpositive : Q.family.PositiveAt (Q.x 0)) (hgate : Q.family.Gate (Q.x 0) η)
    (hη : L.terminalGate ≤ η) :
    ∃ J : SupportedPath (AttachmentSpace V PhaseSpace) μ (List.ofFn L.path.steps++List.ofFn Q.steps).length,
      List.ofFn J.steps = List.ofFn L.path.steps++List.ofFn Q.steps ∧
      J.x 0 = alignedAttachment (L.path.x (Fin.last _)) (Q.x 0) (L.path.x 0) ∧
      J.x (Fin.last _) = retainedMap (W := PhaseSpace) (Q.x (Fin.last m)) ∧
      J.x 0 ≠ 0 ∧ J.family.PositiveAt (J.x 0) ∧ J.family.Gate (J.x 0) (d/L.sourceSlopeCap) ∧
      (∀ k, inner ℝ (J.x 0) (J.family.g k) ≤
        (‖Q.x 0‖/‖L.path.x (Fin.last _)‖)^2*L.sourceSlopeCap) ∧
      (∀ k, max (inner ℝ (J.x 0) (J.family.z k)-
        ((L.sourceHeightOffset+‖L.R‖*d)/‖L.path.x 0‖^2)*‖J.x 0‖^2) 0/‖L.R‖ ≤ J.family.d k) ∧
      ‖J.x (Fin.last _)‖^2/‖J.x 0‖^2 =
        (‖Q.x (Fin.last m)‖^2/‖Q.x 0‖^2)*
          (‖L.path.x (Fin.last _)‖^2/‖L.path.x 0‖^2) ∧
      ∀ k, AttachmentOrigin L.path.family Q.family (L.path.x (Fin.last _)) (Q.x 0) d
        (J.family.z k) (J.family.g k) (J.family.d k) := by
  have hfloor : ∀ i, d ≤ L.path.family.d i := fun i => hdheight.trans (L.height_floor i)
  have hproject : ∀ i, inner ℝ (L.path.x (Fin.last _)) (L.path.family.z i) ≤ η*‖L.path.x (Fin.last _)‖^2 := by
    intro i
    exact (L.terminal_gate_bound i).trans (mul_le_mul_of_nonneg_right hη (sq_nonneg _))
  obtain ⟨J,hstart,hend,hsteps,horigin⟩ := L.path.exists_attached Q L.endpoint_ne_zero hY hd hfloor
    L.endpoint_slopes_nonpositive hpositive hgate hproject
  have hX := L.path.source_ne_zero L.endpoint_ne_zero
  have hprop := attachment_source_properties L.path.family Q.family J.family L.endpoint_ne_zero hY
    L.orthogonal L.positive_at_source hd L.sourceSlopeCap_positive hfloor L.source_slope_bound horigin
  refine ⟨J,hsteps,hstart,hend,?_,?_,?_,?_,?_,?_,horigin⟩
  · rw [hstart]
    exact alignedAttachment_ne_zero L.endpoint_ne_zero hY hX
  · rw [hstart]
    exact hprop.1
  · rw [hstart]
    exact hprop.2
  · intro k
    rw [hstart]
    exact attachment_source_slope_cap L.path.family Q.family J.family L.endpoint_ne_zero hY L.orthogonal
      L.sourceSlopeCap_positive.le L.source_slope_bound horigin k
  · intro k
    rw [hstart]
    exact attachment_height L.path.family Q.family J.family L.endpoint_ne_zero hY hX L.orthogonal
      hd (norm_pos_iff.mpr L.R_ne_zero) L.source_height_offset_nonnegative L.source_height_bound horigin k
  · rw [hstart,hend]
    exact attachment_ratio L.endpoint_ne_zero hY (Q.x (Fin.last m))

end
end StrongSilver.LocalPhaseCertificate
