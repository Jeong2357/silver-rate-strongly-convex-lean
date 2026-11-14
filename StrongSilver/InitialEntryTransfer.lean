-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.InitialTwoSidedAttachment
import StrongSilver.ExponentialEntryRatio

namespace StrongSilver
open Real Filter
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
set_option maxHeartbeats 2000000

theorem eventually_initial_zero_slope_entry : ∀ᶠ A : ℝ in atTop,
    ∀ μ b T κ B : ℝ, ∀ h : List ℝ, InitialPhaseBudget A μ b T κ B h →
      ∀ m : ℕ, ∀ Q : SupportedPath V μ m, Q.x 0 ≠ 0 → ∀ v u : ℝ, 0 < v →
      ‖Q.x 0‖ ≤ Real.exp u*v → v ≤ ‖Q.x (Fin.last m)‖ →
      (∀ j, |inner ℝ (unitDirection (Q.x 0)) (Q.family.z j)| ≤ Real.exp u*v) →
      (∀ j, Q.family.g j = 0) →
      ∃ n : ℕ, ∃ J : SupportedPath (AttachmentSpace V PhaseSpace) μ n,
        List.ofFn J.steps = (h++[b])++List.ofFn Q.steps ∧
        J.x (Fin.last n) = retainedMap (W := PhaseSpace) (Q.x (Fin.last m)) ∧
        J.x 0 ≠ 0 ∧ J.family.PositiveAt (J.x 0) ∧ J.family.Gate (J.x 0) (initialGateConstant/(κ/B)^2) ∧
        (∀ j, |inner ℝ (unitDirection (J.x 0)) (J.family.z j)| ≤ initialPointRelativeConstant*(κ/B)*‖J.x 0‖ ∧
          |inner ℝ (unitDirection (J.x 0)) (J.family.g j)| ≤ initialSlopeRelativeConstant*(κ/B)*‖J.x 0‖/κ) ∧
        Real.exp (-2*u)/(2*initialEntryConstant*(κ/B)^4) ≤ ‖J.x (Fin.last n)‖^2/‖J.x 0‖^2 := by
  filter_upwards [eventually_initial_two_sided_attachment] with A hattach
  intro μ b T κ B h W m Q hQ v u hv hN hE hz hg
  let R := Real.exp u*v
  have hR : 0 < R := mul_pos (Real.exp_pos _) hv
  have hgz (j) : |inner ℝ (unitDirection (Q.x 0)) (Q.family.g j)| ≤ 0 := by rw [hg,inner_zero_right,abs_zero]
  obtain ⟨n,J,hsteps,hend,hNZ,hPos,hGate,hNsq,hrelative⟩ :=
    hattach μ b T κ B h W V m Q hQ R 0 hR.le le_rfl hz hgz
  have hUsq := (sq_le_sq₀ (norm_nonneg (Q.x 0)) hR.le).mpr hN
  have hUR := mul_le_mul_of_nonneg_right hN hR.le
  have hsum : ‖Q.x 0‖^2+‖Q.x 0‖*R+κ*‖Q.x 0‖*0 ≤ 2*R^2 := by nlinarith only [hUsq,hUR]
  have hK : 0 < κ/B := div_pos W.kappa_positive W.B_positive
  have hC0 := initialEntryConstant_positive
  have hC : 0 < initialEntryConstant*(κ/B)^4 := mul_pos initialEntryConstant_positive (pow_pos hK 4)
  have hscale := mul_le_mul_of_nonneg_left hsum hC.le
  have hEntry : ‖J.x 0‖^2 ≤ (2*initialEntryConstant*(κ/B)^4)*(Real.exp u*v)^2 := by nlinarith only [hNsq,hscale]
  have hEndNorm : ‖J.x (Fin.last _)‖ = ‖Q.x (Fin.last m)‖ := by rw [hend]; exact retainedIsometry.norm_map _
  have hElower : v ≤ ‖J.x (Fin.last _)‖ := hE.trans_eq hEndNorm.symm
  have hratio := ratio_lower_of_exponential_entry hv (norm_pos_iff.mpr hNZ)
    (by positivity : 0 < 2*initialEntryConstant*(κ/B)^4) hElower hEntry
  exact ⟨n,J,hsteps,hend,hNZ,hPos,hGate,hrelative,hratio⟩

end
end StrongSilver
