-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.OrdinaryRootPad
import StrongSilver.WorkingOrdinarySuffixOffset
import StrongSilver.OrdinaryFourPhaseSuffix
import StrongSilver.OrdinaryPhaseAttachment

namespace StrongSilver
open Real Filter Scalar.SignedIntervals
noncomputable section
set_option maxHeartbeats 2600000

/-- The right ordinary gap in Lemma 4.2 produces an actual retained
suffix for every four-phase group. The source cap and offset decay are
conclusions from an original large root and its negative-step budget. -/
theorem eventually_ordinary_root_suffix : ∀ᶠ A : ℝ in atTop,
    ∀ μ b T P : ℝ, ∀ h : List ℝ, OrdinaryPhaseParameters A μ b T P h →
    ∀ i : Fin h.length, A^((499:ℝ)/500) ≤ h.get i → negativeMass h ≤ h.get i/16 →
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
      [ProperSpace (AttachmentSpace V PhaseSpace)],
    ∀ m : ℕ, ∀ Q : SupportedPath V μ m, Q.x 0 ≠ 0 → Q.family.PositiveAt (Q.x 0) →
      Q.family.Gate (Q.x 0) (workingGateFraction A) →
    ∃ e > 0, ∃ L : LocalPhaseCertificate A μ b T e h, ∃ n : ℕ,
    ∃ J : SupportedPath (AttachmentSpace V PhaseSpace) μ n,
      e^2 = A^(-(3:ℝ)/25)*T*(‖L.R‖+P) ∧
      List.ofFn J.steps = (h++[b])++List.ofFn Q.steps ∧
      J.x 0 = alignedAttachment (L.path.x (Fin.last _)) (Q.x 0) (L.path.x 0) ∧
      J.x (Fin.last n) = retainedMap (W := PhaseSpace) (Q.x (Fin.last m)) ∧
      FourPhaseSuffixBounds J.family (J.x 0) (‖L.R‖/8)
        ((L.sourceHeightOffset+‖L.R‖*(workingGateFraction A*L.sourceSlopeCap))/‖L.path.x 0‖^2) ∧
      (L.sourceHeightOffset+‖L.R‖*(workingGateFraction A*L.sourceSlopeCap))/‖L.path.x 0‖^2 ≤ A^(-(1:ℝ)/20) ∧
      J.family.Gate (J.x 0) (workingGateFraction A) ∧
      ((b-P)/(transformedGapMaximum μ h+P))*Real.exp (-(1200/Real.log A+μ*transformedGapMaximum μ h)) ≤
        ‖L.path.x (Fin.last _)‖/‖L.path.x 0‖ ∧
      ‖J.x (Fin.last n)‖^2/‖J.x 0‖^2 =
        (‖Q.x (Fin.last m)‖^2/‖Q.x 0‖^2)*(‖L.path.x (Fin.last _)‖^2/‖L.path.x 0‖^2) := by
  filter_upwards [eventually_gt_atTop (0:ℝ),eventually_exists_ordinary_phase,
    eventually_root_pad_le_planar_norm,eventually_working_suffix_offset_decay]
    with A hA hex hpad hoff
  intro μ b T P h W i hroot hnegative V _ _ _ m Q hY hpos hgate
  obtain ⟨e,he,L,hscale,hgateOld,hgateNew,hgain⟩ := hex μ b T P h W
  have hPM := hpad μ b T e P h L i hroot W.pad_upper hnegative
  obtain ⟨hcap,hZ⟩ := hoff μ b T e P h L W hscale hPM
  let d := workingGateFraction A*L.sourceSlopeCap
  have hd : 0 ≤ d := mul_nonneg (Real.rpow_pos_of_pos hA _).le L.sourceSlopeCap_positive.le
  obtain ⟨J,hword,hs,heJ,hB,hg,hr⟩ := L.exists_four_phase_suffix Q hY hd hgateNew hpos hgate hgateOld hcap
  have hcancel : d/L.sourceSlopeCap = workingGateFraction A :=
    mul_div_cancel_right₀ _ L.sourceSlopeCap_positive.ne'
  rw [hcancel] at hg
  refine ⟨e,he,L,_,J,hscale,?_,hs,heJ,hB,hZ,hg,hgain,hr⟩
  rw [hword,L.step_list]

end
end StrongSilver
