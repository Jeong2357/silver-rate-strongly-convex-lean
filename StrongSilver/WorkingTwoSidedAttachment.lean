-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.RaisedWorkingPhase
import StrongSilver.RaisedSourceNorm
import StrongSilver.WorkingLocalQueryBounds
import StrongSilver.AttachmentRelativeBounds

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 1800000

/-- A working-band phase can be put before any nonzero supported suffix with
finite two-sided directional bounds. Its scalar height is chosen explicitly,
and the resulting source is positive with the common working-band gate. -/
theorem eventually_working_two_sided_attachment : ∀ᶠ A : ℝ in atTop,
    ∀ μ b T P : ℝ, ∀ h : List ℝ, OrdinaryPhaseParameters A μ b T P h →
      ∀ (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [ProperSpace (AttachmentSpace V PhaseSpace)],
      ∀ m : ℕ, ∀ Q : SupportedPath V μ m, Q.x 0 ≠ 0 → ∀ Z H : ℝ, 0 ≤ Z → 0 ≤ H →
      (∀ j, |inner ℝ (unitDirection (Q.x 0)) (Q.family.z j)| ≤ Z) →
      (∀ j, |inner ℝ (unitDirection (Q.x 0)) (Q.family.g j)| ≤ H) →
      ∃ e : ℝ, 0 < e ∧ ∃ L : LocalPhaseCertificate A μ b T e h,
        e^2 = A^(-(3 : ℝ)/25)*T*(‖L.R‖+
          raisedPhasePadding A (‖Q.x 0‖/‖L.path.x (Fin.last _)‖) Z H) ∧
        ∃ J : SupportedPath (AttachmentSpace V PhaseSpace) μ (List.ofFn L.path.steps++List.ofFn Q.steps).length,
          List.ofFn J.steps = (h++[b])++List.ofFn Q.steps ∧
          J.x 0 = alignedAttachment (L.path.x (Fin.last _)) (Q.x 0) (L.path.x 0) ∧
          J.x (Fin.last _) = retainedMap (W := PhaseSpace) (Q.x (Fin.last m)) ∧
          J.x 0 ≠ 0 ∧ J.family.PositiveAt (J.x 0) ∧ J.family.Gate (J.x 0) (workingGateFraction A) ∧
          ‖J.x 0‖^2 ≤ A^(19 : ℝ)*(‖Q.x 0‖^2+‖Q.x 0‖*Z+‖Q.x 0‖*H) ∧
          (∀ k, |inner ℝ (unitDirection (J.x 0)) (J.family.z k)| ≤ A^(10 : ℝ)*‖J.x 0‖ ∧
            |inner ℝ (unitDirection (J.x 0)) (J.family.g k)| ≤ A^(10 : ℝ)*‖J.x 0‖) ∧
          ‖J.x (Fin.last _)‖^2/‖J.x 0‖^2 =
            (‖Q.x (Fin.last m)‖^2/‖Q.x 0‖^2)*(‖L.path.x (Fin.last _)‖^2/‖L.path.x 0‖^2) := by
  filter_upwards [eventually_gt_atTop (0 : ℝ),eventually_exists_raised_working_phase,
    eventually_raised_source_norm,eventually_working_local_relative_queries] with A hA hraised hnorm hqueries
  intro μ b T P h W V _ _ _ m Q hY Z H hZ hH holdz holdg
  obtain ⟨e,he0,L,he,d,hd,hdheight,hdgate,hcostz,hcostg,hplanar⟩ :=
    hraised μ b T P ‖Q.x 0‖ Z H h W (norm_pos_iff.mpr hY) hZ hH
  obtain ⟨J,hsteps,hsource,hend,hNZ,hPos,hGate,hRatio,horigin⟩ := L.exists_two_sided_phase_attachment Q hY hd
    hdheight hplanar holdz holdg hcostz hcostg
  have hη : workingGateFraction A ≤ d/L.sourceSlopeCap := (le_div_iff₀ L.sourceSlopeCap_positive).mpr hdgate
  refine ⟨e,he0,L,he,J,?_,hsource,hend,hNZ,hPos,?_,?_,?_,hRatio⟩
  · exact hsteps.trans (congrArg (fun l : List ℝ => l++List.ofFn Q.steps) (List.ofFn_get (h++[b])))
  · exact J.family.gate_below hPos.2 hGate hη
  · let s := ‖Q.x 0‖/‖L.path.x (Fin.last _)‖
    have hs : 0 < s := div_pos (norm_pos_iff.mpr hY) (norm_pos_iff.mpr L.endpoint_ne_zero)
    have hsU : s ≤ ‖Q.x 0‖ := by
      apply (div_le_iff₀ (norm_pos_iff.mpr L.endpoint_ne_zero)).mpr
      have hE : 1 ≤ ‖L.path.x (Fin.last _)‖ := by linarith [L.endpoint_norm_lower,L.b_large]
      nlinarith only [hE,norm_nonneg (Q.x 0)]
    have hlocal := hnorm μ b T e P s Z H h W L hs hZ hH he
    rw [hsource,alignedAttachment_norm_sq L.endpoint_ne_zero hY]
    exact scaled_raised_source_norm hA hs hsU hZ hH hlocal
  · let s := ‖Q.x 0‖/‖L.path.x (Fin.last _)‖
    have hs : 0 < s := div_pos (norm_pos_iff.mpr hY) (norm_pos_iff.mpr L.endpoint_ne_zero)
    have hratio : 1 ≤ 1+(Z+H)/s := by have := div_nonneg (add_nonneg hZ hH) hs.le; linarith
    have hP : A^(10 : ℝ) ≤ raisedPhasePadding A s Z H := by
      have hh := mul_le_mul_of_nonneg_left hratio (Real.rpow_pos_of_pos hA (10 : ℝ)).le
      simpa only [raisedPhasePadding,mul_one] using hh
    have hPsmall := (Real.rpow_le_rpow_of_exponent_le L.planar.large.le (by norm_num : (49 : ℝ)/50 ≤ 10)).trans hP
    have hlocal := hqueries μ b T e P h W L (raisedPhasePadding A s Z H) hPsmall he
    intro k
    rw [hsource]
    exact attachment_relative_bounds L.path.family Q.family J.family L.endpoint_ne_zero hY
      (L.path.source_ne_zero L.endpoint_ne_zero) L.orthogonal (Real.rpow_pos_of_pos hA (10 : ℝ)).le hlocal horigin k

end
end StrongSilver
