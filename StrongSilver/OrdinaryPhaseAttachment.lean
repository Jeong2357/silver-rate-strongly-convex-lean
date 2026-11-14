-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.OrdinaryPhaseConstruction
import StrongSilver.PhaseAttachment
import StrongSilver.WorkingLocalQueryBounds
import StrongSilver.AttachmentRelativeBounds

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 2000000

theorem LocalPhaseCertificate.step_list {A μ b T e : ℝ} {h : List ℝ}
    (L : LocalPhaseCertificate A μ b T e h) : List.ofFn L.path.steps = h++[b] := List.ofFn_get _

/-- An ordinary phase preserves the working gate and realizes the reference
product factor on an actual compatible trajectory. -/
theorem eventually_ordinary_phase_attachment : ∀ᶠ A : ℝ in atTop,
    ∀ μ b T P : ℝ, ∀ h : List ℝ, OrdinaryPhaseParameters A μ b T P h →
      ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
        [ProperSpace (AttachmentSpace V PhaseSpace)],
      ∀ m : ℕ, ∀ Q : SupportedPath V μ m, Q.x 0 ≠ 0 → Q.family.PositiveAt (Q.x 0) →
        Q.family.Gate (Q.x 0) (workingGateFraction A) →
      ∃ n : ℕ, ∃ J : SupportedPath (AttachmentSpace V PhaseSpace) μ n,
        List.ofFn J.steps = (h++[b])++List.ofFn Q.steps ∧ J.x 0 ≠ 0 ∧
        J.family.PositiveAt (J.x 0) ∧ J.family.Gate (J.x 0) (workingGateFraction A) ∧
        (∀ k, |inner ℝ (unitDirection (J.x 0)) (J.family.z k)| ≤ A^(10 : ℝ)*‖J.x 0‖ ∧
          |inner ℝ (unitDirection (J.x 0)) (J.family.g k)| ≤ A^(10 : ℝ)*‖J.x 0‖) ∧
        (‖Q.x (Fin.last m)‖^2/‖Q.x 0‖^2)*
          (((b-P)/(transformedGapMaximum μ h+P))*Real.exp (-(1200/Real.log A+μ*transformedGapMaximum μ h)))^2 ≤
          ‖J.x (Fin.last n)‖^2/‖J.x 0‖^2 := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),eventually_exists_ordinary_phase,
    eventually_working_local_relative_queries] with A hA hex hqueries
  intro μ b T P h W V _ _ _ m Q hY hpositive hgate
  obtain ⟨e,he,L,hscale,hgateOld,hheight,hgain⟩ := hex μ b T P h W
  have hη : 0 ≤ workingGateFraction A := (Real.rpow_pos_of_pos (zero_lt_one.trans hA) _).le
  let d := workingGateFraction A*L.sourceSlopeCap
  have hd : 0 ≤ d := mul_nonneg hη L.sourceSlopeCap_positive.le
  obtain ⟨J,hsteps,hstart,hend,hJ0,hJpositive,hJgate,hcap,hht,hratio,horigin⟩ :=
    L.exists_phase_attachment Q hY hd hheight hpositive hgate hgateOld
  have hcancel : d/L.sourceSlopeCap = workingGateFraction A := by
    dsimp [d]
    exact mul_div_cancel_right₀ _ L.sourceSlopeCap_positive.ne'
  rw [hcancel] at hJgate
  have hPb : P ≤ b := W.pad_upper.trans ((Real.rpow_le_rpow_of_exponent_le hA.le
    (by norm_num : (199 : ℝ)/200 ≤ 499/500)).trans W.pivot_lower)
  have hP0 : 0 < P := (Real.rpow_pos_of_pos (zero_lt_one.trans hA) _).trans_le W.pad_lower
  have hm := transformedGapMaximum_nonnegative L.mu_positive h L.small_steps
  have hfactor : 0 ≤ ((b-P)/(transformedGapMaximum μ h+P))*Real.exp (-(1200/Real.log A+μ*transformedGapMaximum μ h)) :=
    mul_nonneg (div_nonneg (sub_nonneg.mpr hPb) (add_nonneg hm hP0.le)) (Real.exp_pos _).le
  have hsquared : (((b-P)/(transformedGapMaximum μ h+P))*Real.exp (-(1200/Real.log A+μ*transformedGapMaximum μ h)))^2 ≤
      (‖L.path.x (Fin.last _)‖/‖L.path.x 0‖)^2 := by
    nlinarith only [hgain,hfactor,div_nonneg (norm_nonneg (L.path.x (Fin.last _))) (norm_nonneg (L.path.x 0))]
  rw [div_pow] at hsquared
  have hmul := mul_le_mul_of_nonneg_left hsquared (div_nonneg (sq_nonneg ‖Q.x (Fin.last m)‖) (sq_nonneg ‖Q.x 0‖))
  rw [← hratio] at hmul
  have hsteps' : List.ofFn J.steps = (h++[b])++List.ofFn Q.steps :=
    hsteps.trans (congrArg (fun l : List ℝ => l++List.ofFn Q.steps) L.step_list)
  refine ⟨_,J,hsteps',hJ0,hJpositive,hJgate,?_,hmul⟩
  intro k
  rw [hstart]
  exact attachment_relative_bounds L.path.family Q.family J.family L.endpoint_ne_zero hY
    (L.path.source_ne_zero L.endpoint_ne_zero) L.orthogonal (Real.rpow_pos_of_pos (zero_lt_one.trans hA) (10 : ℝ)).le
    (hqueries μ b T e P h W L P W.pad_lower hscale) horigin k

end
end StrongSilver
