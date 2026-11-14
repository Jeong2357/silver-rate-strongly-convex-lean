-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.WorkingTwoSidedAttachment
import StrongSilver.ExponentialEntryRatio

namespace StrongSilver
open Real Filter
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
set_option maxHeartbeats 2000000

theorem eventually_working_zero_slope_entry : ∀ᶠ A : ℝ in atTop,
    ∀ μ b T P : ℝ, ∀ h : List ℝ, OrdinaryPhaseParameters A μ b T P h →
      ∀ m : ℕ, ∀ Q : SupportedPath V μ m, Q.x 0 ≠ 0 → ∀ v u : ℝ, 0 < v →
      ‖Q.x 0‖ ≤ Real.exp u*v → v ≤ ‖Q.x (Fin.last m)‖ →
      (∀ j, |inner ℝ (unitDirection (Q.x 0)) (Q.family.z j)| ≤ Real.exp u*v) →
      (∀ j, Q.family.g j = 0) →
      ∃ n : ℕ, ∃ J : SupportedPath (AttachmentSpace V PhaseSpace) μ n,
        List.ofFn J.steps = (h++[b])++List.ofFn Q.steps ∧
        J.x (Fin.last n) = retainedMap (W := PhaseSpace) (Q.x (Fin.last m)) ∧
        J.x 0 ≠ 0 ∧ J.family.PositiveAt (J.x 0) ∧ J.family.Gate (J.x 0) (workingGateFraction A) ∧
        (∀ j, |inner ℝ (unitDirection (J.x 0)) (J.family.z j)| ≤ A^(10 : ℝ)*‖J.x 0‖ ∧
          |inner ℝ (unitDirection (J.x 0)) (J.family.g j)| ≤ A^(10 : ℝ)*‖J.x 0‖) ∧
        Real.exp (-2*u)/(2*A^(19 : ℝ)) ≤ ‖J.x (Fin.last n)‖^2/‖J.x 0‖^2 := by
  filter_upwards [eventually_gt_atTop (0 : ℝ),eventually_working_two_sided_attachment]
    with A hA hattach
  intro μ b T P h W m Q hQ v u hv hN hE hz hg
  let R := Real.exp u*v
  have hR : 0 < R := mul_pos (Real.exp_pos _) hv
  have hgz (j) : |inner ℝ (unitDirection (Q.x 0)) (Q.family.g j)| ≤ 0 := by rw [hg,inner_zero_right,abs_zero]
  obtain ⟨e,he0,L,he,J,hsteps,hsource,hend,hNZ,hPos,hGate,hNsq,hrelative,hRatio⟩ :=
    hattach μ b T P h W V m Q hQ R 0 hR.le le_rfl hz hgz
  have hUsq := (sq_le_sq₀ (norm_nonneg (Q.x 0)) hR.le).mpr hN
  have hUR := mul_le_mul_of_nonneg_right hN hR.le
  have hsum : ‖Q.x 0‖^2+‖Q.x 0‖*R+‖Q.x 0‖*0 ≤ 2*R^2 := by nlinarith only [hUsq,hUR]
  have hscale := mul_le_mul_of_nonneg_left hsum (Real.rpow_pos_of_pos hA (19 : ℝ)).le
  have hEntry : ‖J.x 0‖^2 ≤ (2*A^(19 : ℝ))*(Real.exp u*v)^2 := by nlinarith only [hNsq,hscale]
  have hEndNorm : ‖J.x (Fin.last _)‖ = ‖Q.x (Fin.last m)‖ := by rw [hend]; exact retainedIsometry.norm_map _
  have hElower : v ≤ ‖J.x (Fin.last _)‖ := hE.trans_eq hEndNorm.symm
  have hratio := ratio_lower_of_exponential_entry hv (norm_pos_iff.mpr hNZ)
    (by positivity : 0 < 2*A^(19 : ℝ)) hElower hEntry
  exact ⟨_,J,hsteps,hend,hNZ,hPos,hGate,hrelative,hratio⟩

end
end StrongSilver
