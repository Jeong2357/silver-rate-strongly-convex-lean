-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.NormalizedTerminalPath
import StrongSilver.WorkingEntryTransfer
import StrongSilver.InitialEntryTransfer
import StrongSilver.PhaseCurvatureBounds

namespace StrongSilver
open Real Filter
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
set_option maxHeartbeats 2000000

theorem normalized_terminal_ratio {μ A : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1) (hcap : μ*A ≤ 1/2)
    (I t : List ℝ) (hcritical : ∀ b ∈ I, 1-μ*b ≠ 0) (ht : ∀ b ∈ t, 0 < b → b ≤ A)
    {Y : V} (hY : Y ≠ 0) :
    ∃ Q : SupportedPath V μ (I++t).length, List.ofFn Q.steps = I++t ∧ Q.x (Fin.last _) = Y ∧ Q.x 0 ≠ 0 ∧
      Real.exp (-2*(inverseCharge μ I+2*μ*Scalar.SignedIntervals.positiveMass t)) ≤ ‖Q.x (Fin.last _)‖^2/‖Q.x 0‖^2 := by
  obtain ⟨Q,hsteps,hend,hQ,hN,hz,hg,hgate⟩ := normalized_terminal_path hμ hμ1 hcap I t hcritical ht hY
  have hv : 0 < ‖Y‖ := norm_pos_iff.mpr hY
  have hR : 0 < Real.exp (inverseCharge μ I+2*μ*Scalar.SignedIntervals.positiveMass t)*‖Y‖ := mul_pos (Real.exp_pos _) hv
  have hNsq := (sq_le_sq₀ (norm_nonneg (Q.x 0)) hR.le).mpr hN
  have hratio := ratio_lower_of_exponential_entry hv (norm_pos_iff.mpr hQ) zero_lt_one
    (show ‖Y‖ ≤ ‖Q.x (Fin.last _)‖ by rw [hend]) (by simpa only [one_mul] using hNsq)
  refine ⟨Q,hsteps,hend,hQ,?_⟩
  simpa only [div_one] using hratio

theorem eventually_working_no_connector_terminal : ∀ᶠ A : ℝ in atTop,
    ∀ μ b T P : ℝ, ∀ h I t : List ℝ, OrdinaryPhaseParameters A μ b T P h →
      (∀ a ∈ I, 1-μ*a ≠ 0) → (∀ a ∈ t, 0 < a → a ≤ A) → ∀ Y : V, Y ≠ 0 →
      ∃ n : ℕ, ∃ J : SupportedPath (AttachmentSpace V PhaseSpace) μ n,
        List.ofFn J.steps = (h++[b])++(I++t) ∧ J.x (Fin.last n) = retainedMap (W := PhaseSpace) Y ∧
        J.x 0 ≠ 0 ∧ J.family.PositiveAt (J.x 0) ∧ J.family.Gate (J.x 0) (workingGateFraction A) ∧
        (∀ j, |inner ℝ (unitDirection (J.x 0)) (J.family.z j)| ≤ A^(10 : ℝ)*‖J.x 0‖ ∧
          |inner ℝ (unitDirection (J.x 0)) (J.family.g j)| ≤ A^(10 : ℝ)*‖J.x 0‖) ∧
        Real.exp (-2*(inverseCharge μ I+2*μ*Scalar.SignedIntervals.positiveMass t))/(2*A^(19 : ℝ)) ≤
          ‖J.x (Fin.last n)‖^2/‖J.x 0‖^2 := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),eventually_working_zero_slope_entry (V := V)] with A hA hentry
  intro μ b T P h I t W hcritical ht Y hY
  obtain ⟨Q,hstepsQ,hendQ,hQ,hN,hz,hg,hgate⟩ := normalized_terminal_path W.mu_positive (W.mu_lt_one hA).le
    (W.mu_cap (zero_lt_one.trans_le hA)) I t hcritical ht hY
  obtain ⟨n,J,hsteps,hend,hNZ,hPos,hGate,hrel,hRatio⟩ := hentry μ b T P h W (I++t).length Q hQ ‖Y‖
    (inverseCharge μ I+2*μ*Scalar.SignedIntervals.positiveMass t) (norm_pos_iff.mpr hY) hN
    (by rw [hendQ]) hz hg
  refine ⟨n,J,?_,?_,hNZ,hPos,hGate,hrel,hRatio⟩
  · exact hsteps.trans (congrArg (fun l : List ℝ => (h++[b])++l) hstepsQ)
  · exact hend.trans (congrArg (retainedMap (W := PhaseSpace)) hendQ)

theorem eventually_initial_no_connector_terminal : ∀ᶠ A : ℝ in atTop,
    ∀ μ b T κ B : ℝ, ∀ h I t : List ℝ, InitialPhaseBudget A μ b T κ B h → μ*B ≤ 1/2 →
      (∀ a ∈ I, 1-μ*a ≠ 0) → (∀ a ∈ t, 0 < a → a ≤ B) → ∀ Y : V, Y ≠ 0 →
      ∃ n : ℕ, ∃ J : SupportedPath (AttachmentSpace V PhaseSpace) μ n,
        List.ofFn J.steps = (h++[b])++(I++t) ∧ J.x (Fin.last n) = retainedMap (W := PhaseSpace) Y ∧
        J.x 0 ≠ 0 ∧ J.family.PositiveAt (J.x 0) ∧ J.family.Gate (J.x 0) (initialGateConstant/(κ/B)^2) ∧
        (∀ j, |inner ℝ (unitDirection (J.x 0)) (J.family.z j)| ≤ initialPointRelativeConstant*(κ/B)*‖J.x 0‖ ∧
          |inner ℝ (unitDirection (J.x 0)) (J.family.g j)| ≤ initialSlopeRelativeConstant*(κ/B)*‖J.x 0‖/κ) ∧
        Real.exp (-2*(inverseCharge μ I+2*μ*Scalar.SignedIntervals.positiveMass t))/(2*initialEntryConstant*(κ/B)^4) ≤
          ‖J.x (Fin.last n)‖^2/‖J.x 0‖^2 := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),eventually_initial_zero_slope_entry (V := V)] with A hA hentry
  intro μ b T κ B h I t W hcap hcritical ht Y hY
  obtain ⟨Q,hstepsQ,hendQ,hQ,hN,hz,hg,hgate⟩ := normalized_terminal_path W.mu_positive (W.mu_lt_one hA).le hcap I t hcritical ht hY
  obtain ⟨n,J,hsteps,hend,hNZ,hPos,hGate,hrel,hRatio⟩ := hentry μ b T κ B h W (I++t).length Q hQ ‖Y‖
    (inverseCharge μ I+2*μ*Scalar.SignedIntervals.positiveMass t) (norm_pos_iff.mpr hY) hN
    (by rw [hendQ]) hz hg
  refine ⟨n,J,?_,?_,hNZ,hPos,hGate,hrel,hRatio⟩
  · exact hsteps.trans (congrArg (fun l : List ℝ => (h++[b])++l) hstepsQ)
  · exact hend.trans (congrArg (retainedMap (W := PhaseSpace)) hendQ)

end
end StrongSilver
