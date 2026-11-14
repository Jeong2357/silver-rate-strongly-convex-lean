-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.InitialRaisedPhase
import StrongSilver.InitialQueryBounds
import StrongSilver.TwoSidedPhaseAttachment
import StrongSilver.AttachmentRelativeBounds

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 2400000

/-- Initial-cutoff attachment before a two-sided suffix. The height and all
constants are constructed. The source price is polynomial in kappa/B, and
the new gate and projection bounds are uniform in the retained suffix. -/
theorem eventually_initial_two_sided_attachment : ∀ᶠ A : ℝ in atTop,
    ∀ μ b T κ B : ℝ, ∀ h : List ℝ, InitialPhaseBudget A μ b T κ B h →
      ∀ (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V],
      ∀ m : ℕ, ∀ Q : SupportedPath V μ m, Q.x 0 ≠ 0 → ∀ Z H : ℝ, 0 ≤ Z → 0 ≤ H →
      (∀ j, |inner ℝ (unitDirection (Q.x 0)) (Q.family.z j)| ≤ Z) →
      (∀ j, |inner ℝ (unitDirection (Q.x 0)) (Q.family.g j)| ≤ H) →
      ∃ n : ℕ, ∃ J : SupportedPath (AttachmentSpace V PhaseSpace) μ n,
        List.ofFn J.steps = (h++[b])++List.ofFn Q.steps ∧
        J.x (Fin.last n) = retainedMap (W := PhaseSpace) (Q.x (Fin.last m)) ∧
        J.x 0 ≠ 0 ∧ J.family.PositiveAt (J.x 0) ∧ J.family.Gate (J.x 0) (initialGateConstant/(κ/B)^2) ∧
        ‖J.x 0‖^2 ≤ initialEntryConstant*(κ/B)^4*(‖Q.x 0‖^2+‖Q.x 0‖*Z+κ*‖Q.x 0‖*H) ∧
        (∀ k, |inner ℝ (unitDirection (J.x 0)) (J.family.z k)| ≤ initialPointRelativeConstant*(κ/B)*‖J.x 0‖ ∧
          |inner ℝ (unitDirection (J.x 0)) (J.family.g k)| ≤ initialSlopeRelativeConstant*(κ/B)*‖J.x 0‖/κ) := by
  filter_upwards [eventually_exists_initial_phase] with A hex
  intro μ b T κ B h W V _ _ _ m Q hY Z H hZ hH holdz holdg
  obtain ⟨L₀⟩ := hex μ b T κ B h W
  obtain ⟨e,he0,L,heκ,he,d,hd,hdheight,hFrac,hcostz,hcostg,hN⟩ :=
    exists_initial_raised_phase W L₀ (norm_pos_iff.mpr hY) hZ hH
  obtain ⟨J,hsteps,hsource,hend,hNZ,hPos,hGate,hRatio,horigin⟩ :=
    L.exists_two_sided_phase_attachment Q hY hd hdheight
      (fun j hj => W.planar_all_norm L j) holdz holdg hcostz hcostg
  refine ⟨_,J,?_,hend,hNZ,hPos,?_,?_,?_⟩
  · exact hsteps.trans (congrArg (fun l : List ℝ => l++List.ofFn Q.steps) (List.ofFn_get (h++[b])))
  · exact J.family.gate_below hPos.2 hGate hFrac
  · rw [hsource,alignedAttachment_norm_sq L.endpoint_ne_zero hY]
    exact hN
  · intro k
    rw [hsource]
    exact W.attachment_queries L Q.family J.family hY heκ horigin k

end
end StrongSilver
