-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.TerminalQuadratic
import StrongSilver.TerminalConeRadius
import StrongSilver.TwoConeAttachment

namespace StrongSilver
open Real
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
set_option maxHeartbeats 2000000

theorem terminal_cone_attachment {μ c A : ℝ} (hμ : 0 < μ) (hc : 2 ≤ c) (hqc : 1/32 ≤ 1-μ*c)
    (hcap : μ*A ≤ 1/2) (I t : List ℝ) (hcritical : ∀ b ∈ I, 1-μ*b ≠ 0)
    (ht : ∀ b ∈ t, 0 < b → b ≤ A) {Y : V} (hY : Y ≠ 0) :
    ∃ C : ConeConnectorParameters μ c ‖Y‖ (maxPrefixProduct μ t) 0 1, ∃ n : ℕ,
      ∃ Q : SupportedPath (AttachmentSpace V ℂ) μ n,
        Q.x 0 ≠ 0 ∧ ‖Q.x 0‖ ≤ C.traceRadius I ∧
        Q.x (Fin.last n) = retainedMap (W := ℂ) (quadraticMultiplier μ t • Y) ∧
        List.ofFn Q.steps = (I++[c])++t ∧
        (∀ j, |inner ℝ (unitDirection (Q.x 0)) (Q.family.z j)| ≤ C.traceRadius I+maxPrefixProduct μ t*‖Y‖) ∧
        (∀ j, |inner ℝ (unitDirection (Q.x 0)) (Q.family.g j)| ≤ 2*C.a) ∧
        maxPrefixProduct μ t*Real.exp (-2*μ*Scalar.SignedIntervals.positiveMass t)*‖Y‖ ≤ ‖Q.x (Fin.last n)‖ := by
  have hsmall : ∀ b ∈ t, μ*b < 1 := by
    intro b hb
    by_cases hb0 : 0 < b
    · have hh := (mul_le_mul_of_nonneg_left (ht b hb hb0) hμ.le).trans hcap
      linarith only [hh]
    · have hh := mul_nonpos_of_nonneg_of_nonpos hμ.le (le_of_not_gt hb0)
      linarith only [hh]
  let P := SupportedPath.quadraticRun μ t Y
  have hM : 1 ≤ maxPrefixProduct μ t := maxPrefixProduct_ge_one μ t
  obtain ⟨C,n,Q,hQ,hN,hend,hsteps,hz,hg⟩ := two_cone_attachment hμ hc (by linarith only [hqc])
    (norm_pos_iff.mpr hY) hM le_rfl zero_lt_one le_rfl I hcritical P (unitDirection Y)
    (unitDirection_inner hY) (norm_smul_unitDirection hY).symm
    (SupportedPath.quadraticRun_directional_bound t hsmall hY)
    (fun j => by rw [SupportedPath.quadraticRun_slope,inner_zero_right,abs_zero])
    (SupportedPath.quadraticRun_gate μ t Y 1) (SupportedPath.quadraticRun_gate μ t Y (-1))
  have hend' : Q.x (Fin.last n) = retainedMap (W := ℂ) (quadraticMultiplier μ t • Y) := by
    rw [hend]
    exact congrArg (retainedMap (W := ℂ)) (SupportedPath.quadraticRun_end μ t Y)
  refine ⟨C,n,Q,hQ,hN,hend',?_,hz,?_,?_⟩
  · exact hsteps.trans (congrArg (fun l : List ℝ => (I++[c])++l) (List.ofFn_get t))
  · intro j
    simpa only [add_zero] using hg j
  · rw [hend']
    have hnorm : ‖retainedMap (W := ℂ) (quadraticMultiplier μ t • Y)‖ = ‖quadraticMultiplier μ t • Y‖ := retainedIsometry.norm_map _
    rw [hnorm]
    simpa only [SupportedPath.quadraticRun_end] using SupportedPath.quadraticRun_terminal_gain hμ.le hcap t ht Y

end
end StrongSilver
