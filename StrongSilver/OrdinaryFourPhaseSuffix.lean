-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PhaseAttachment
import StrongSilver.FourPhaseSuffixBounds

namespace StrongSilver.LocalPhaseCertificate
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [ProperSpace (AttachmentSpace V PhaseSpace)]
set_option maxHeartbeats 2400000

/-- The ordinary phase attachment supplies the retained input inequalities
for the four-phase construction. Only its scalar source cap is additional. -/
theorem exists_four_phase_suffix {A μ b T e : ℝ} {h : List ℝ}
    (L : LocalPhaseCertificate A μ b T e h) {m : ℕ} (Q : SupportedPath V μ m)
    (hY : Q.x 0 ≠ 0) {d η : ℝ} (hd : 0 ≤ d)
    (hdheight : d ≤ ((1/T-μ)/32)*Real.exp (-2*negativeLogSum h T)*e^2)
    (hpositive : Q.family.PositiveAt (Q.x 0)) (hgate : Q.family.Gate (Q.x 0) η)
    (hη : L.terminalGate ≤ η) (hcap : L.sourceSlopeCap ≤ 8*‖L.R‖) :
    ∃ J : SupportedPath (AttachmentSpace V PhaseSpace) μ (List.ofFn L.path.steps++List.ofFn Q.steps).length,
      List.ofFn J.steps = List.ofFn L.path.steps++List.ofFn Q.steps ∧
      J.x 0 = alignedAttachment (L.path.x (Fin.last _)) (Q.x 0) (L.path.x 0) ∧
      J.x (Fin.last _) = retainedMap (W := PhaseSpace) (Q.x (Fin.last m)) ∧
      FourPhaseSuffixBounds J.family (J.x 0) (‖L.R‖/8)
        ((L.sourceHeightOffset+‖L.R‖*d)/‖L.path.x 0‖^2) ∧
      J.family.Gate (J.x 0) (d/L.sourceSlopeCap) ∧
      ‖J.x (Fin.last _)‖^2/‖J.x 0‖^2 =
        (‖Q.x (Fin.last m)‖^2/‖Q.x 0‖^2)*(‖L.path.x (Fin.last _)‖^2/‖L.path.x 0‖^2) := by
  obtain ⟨J,hword,hs,he,hnz,hpos,hg,hslopes,hheights,hratio,horigin⟩ :=
    L.exists_phase_attachment Q hY hd hdheight hpositive hgate hη
  have hM : 0 < ‖L.R‖ := norm_pos_iff.mpr L.R_ne_zero
  have hnorm : ‖L.R‖^2 ≤ ‖L.path.x 0‖^2 := by
    rw [L.start,phase_norm_sq]
    nlinarith only [sq_nonneg L.D,sq_nonneg L.scalar.x]
  have hcoef : L.sourceSlopeCap ≤ (11/(10*(‖L.R‖/8)))*‖L.path.x 0‖^2 := by
    have hmul := mul_le_mul_of_nonneg_right hcap hM.le
    have heq : (11/(10*(‖L.R‖/8)))*‖L.path.x 0‖^2 =
        ((44/5:ℝ)*‖L.path.x 0‖^2)/‖L.R‖ := by ring
    rw [heq]
    apply (le_div_iff₀ hM).mpr
    nlinarith only [hmul,hnorm,sq_nonneg ‖L.path.x 0‖]
  have hsourceNorm : ‖J.x 0‖^2 = (‖Q.x 0‖/‖L.path.x (Fin.last _)‖)^2*‖L.path.x 0‖^2 := by
    rw [hs]
    exact alignedAttachment_norm_sq L.endpoint_ne_zero hY _
  have hZ : 0 ≤ (L.sourceHeightOffset+‖L.R‖*d)/‖L.path.x 0‖^2 :=
    div_nonneg (add_nonneg L.source_height_offset_nonnegative (mul_nonneg hM.le hd)) (sq_nonneg _)
  refine ⟨J,hword,hs,he,?_,hg,hratio⟩
  refine ⟨hnz,div_pos hM (by norm_num),hZ,hpos.1,hpos.2,?_,?_⟩
  · intro i
    have hh := mul_le_mul_of_nonneg_left hcoef (sq_nonneg (‖Q.x 0‖/‖L.path.x (Fin.last _)‖))
    rw [hsourceNorm]
    nlinarith only [hslopes i,hh]
  · intro i
    rw [show (8:ℝ)*(‖L.R‖/8) = ‖L.R‖ by ring]
    exact hheights i

end
end StrongSilver.LocalPhaseCertificate
