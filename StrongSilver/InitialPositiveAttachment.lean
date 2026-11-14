-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.InitialTwoSidedAttachment
import StrongSilver.InitialOldGate

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 2000000

/-- Supply the initial gate before an arbitrary positive suffix. The old
point projections need no upper bound. The required gate is (3.28). -/
theorem eventually_initial_positive_attachment : ∀ᶠ A : ℝ in atTop,
    ∀ μ b T κ B : ℝ, ∀ h : List ℝ, InitialPhaseBudget A μ b T κ B h →
      ∀ (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V],
      ∀ m : ℕ, ∀ Q : SupportedPath V μ m, Q.x 0 ≠ 0 → Q.family.PositiveAt (Q.x 0) →
      ∀ η : ℝ, Q.family.Gate (Q.x 0) η → initialOldGate A κ B ≤ η →
      ∃ n : ℕ, ∃ J : SupportedPath (AttachmentSpace V PhaseSpace) μ n,
        List.ofFn J.steps = (h++[b])++List.ofFn Q.steps ∧
        J.x (Fin.last n) = retainedMap (W := PhaseSpace) (Q.x (Fin.last m)) ∧
        J.x 0 ≠ 0 ∧ J.family.PositiveAt (J.x 0) ∧ J.family.Gate (J.x 0) (initialGateConstant/(κ/B)^2) ∧
        ‖J.x 0‖^2 ≤ initialEntryConstant*(κ/B)^4*‖Q.x 0‖^2 ∧
        (∀ k, |inner ℝ (unitDirection (J.x 0)) (J.family.z k)| ≤ initialPointRelativeConstant*(κ/B)*‖J.x 0‖ ∧
          |inner ℝ (unitDirection (J.x 0)) (J.family.g k)| ≤ initialSlopeRelativeConstant*(κ/B)*‖J.x 0‖/κ) := by
  filter_upwards [eventually_exists_initial_phase] with A hex
  intro μ b T κ B h W V _ _ _ m Q hY hpositive η hgate hη
  obtain ⟨L₀⟩ := hex μ b T κ B h W
  obtain ⟨e,he0,L,heκ,he,d,hd,hdheight,hFrac,hcostz,hcostg,hN⟩ :=
    exists_initial_raised_phase W L₀ (Z := 0) (H := 0) (norm_pos_iff.mpr hY) le_rfl le_rfl
  obtain ⟨J,hsteps,hsource,hend,hNZ,hPos,hGate,hcap,hht,hRatio,horigin⟩ :=
    L.exists_phase_attachment Q hY hd hdheight hpositive hgate ((W.old_gate L).trans hη)
  refine ⟨_,J,?_,hend,hNZ,hPos,?_,?_,?_⟩
  · exact hsteps.trans (congrArg (fun l : List ℝ => l++List.ofFn Q.steps) (List.ofFn_get (h++[b])))
  · exact J.family.gate_below hPos.2 hGate hFrac
  · rw [hsource,alignedAttachment_norm_sq L.endpoint_ne_zero hY]
    simpa only [mul_zero,add_zero] using hN
  · intro k
    rw [hsource]
    exact W.attachment_queries L Q.family J.family hY heκ horigin k

end
end StrongSilver
