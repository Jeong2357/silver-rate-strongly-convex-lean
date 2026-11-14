-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.LocalPhaseAbsoluteBounds
import StrongSilver.TwoSidedAttachedPath
import StrongSilver.PhaseAttachment

namespace StrongSilver.LocalPhaseCertificate
open Set Real
noncomputable section
variable {A μ b T e : ℝ} {h : List ℝ} (L : LocalPhaseCertificate A μ b T e h)
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [ProperSpace (AttachmentSpace V PhaseSpace)]
set_option maxHeartbeats 1600000

/-- The exact two-sided phase attachment (3.23), restoring a positive source
and a gate (3.24) before a suffix whose projections may have either sign. -/
theorem exists_two_sided_phase_attachment {m : ℕ} (Q : SupportedPath V μ m) (hY : Q.x 0 ≠ 0)
    {d B Z H : ℝ} (hd : 0 ≤ d)
    (hdheight : d ≤ ((1/T-μ)/32)*Real.exp (-2*negativeLogSum h T)*e^2)
    (hR : ∀ j : ℕ, j ≤ h.length → ‖iterate (h.take j) L.planar.physical L.R‖ ≤ B)
    (holdz : ∀ j, |inner ℝ (unitDirection (Q.x 0)) (Q.family.z j)| ≤ Z)
    (holdg : ∀ j, |inner ℝ (unitDirection (Q.x 0)) (Q.family.g j)| ≤ H)
    (hcostz : (‖Q.x 0‖/‖L.path.x (Fin.last _)‖)*(planarRadius A 0)*Z ≤
      (‖Q.x 0‖/‖L.path.x (Fin.last _)‖)^2*d)
    (hcostg : (‖Q.x 0‖/‖L.path.x (Fin.last _)‖)*(L.endpointProximalCap B)*H ≤
      (‖Q.x 0‖/‖L.path.x (Fin.last _)‖)^2*(((1/T-μ)/32)*Real.exp (-2*negativeLogSum h T)*e^2-d)) :
    ∃ J : SupportedPath (AttachmentSpace V PhaseSpace) μ (List.ofFn L.path.steps++List.ofFn Q.steps).length,
      List.ofFn J.steps = List.ofFn L.path.steps++List.ofFn Q.steps ∧
      J.x 0 = alignedAttachment (L.path.x (Fin.last _)) (Q.x 0) (L.path.x 0) ∧
      J.x (Fin.last _) = retainedMap (W := PhaseSpace) (Q.x (Fin.last m)) ∧
      J.x 0 ≠ 0 ∧ J.family.PositiveAt (J.x 0) ∧ J.family.Gate (J.x 0) (d/L.sourceSlopeCap) ∧
      ‖J.x (Fin.last _)‖^2/‖J.x 0‖^2 =
        (‖Q.x (Fin.last m)‖^2/‖Q.x 0‖^2)*
          (‖L.path.x (Fin.last _)‖^2/‖L.path.x 0‖^2) ∧
      ∀ k, AttachmentOrigin L.path.family Q.family (L.path.x (Fin.last _)) (Q.x 0) d
        (J.family.z k) (J.family.g k) (J.family.d k) := by
  have hfloor : ∀ i, d ≤ L.path.family.d i := fun i => hdheight.trans (L.height_floor i)
  obtain ⟨J,hstart,hend,hsteps,horigin⟩ := L.path.exists_two_sided_attached Q L.endpoint_ne_zero hY hd hdheight
    L.height_floor L.endpoint_slope_absolute (L.endpoint_proximal_absolute hR) holdz holdg hcostz hcostg
  have hX := L.path.source_ne_zero L.endpoint_ne_zero
  have hprop := attachment_source_properties L.path.family Q.family J.family L.endpoint_ne_zero hY
    L.orthogonal L.positive_at_source hd L.sourceSlopeCap_positive hfloor L.source_slope_bound horigin
  refine ⟨J,hsteps,hstart,hend,?_,?_,?_,?_,horigin⟩
  · rw [hstart]
    exact alignedAttachment_ne_zero L.endpoint_ne_zero hY hX
  · rw [hstart]
    exact hprop.1
  · rw [hstart]
    exact hprop.2
  · rw [hstart,hend]
    exact attachment_ratio L.endpoint_ne_zero hY (Q.x (Fin.last m))

end
end StrongSilver.LocalPhaseCertificate
