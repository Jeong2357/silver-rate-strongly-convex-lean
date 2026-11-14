-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.TerminalQuadratic
import StrongSilver.SupportedPathError

namespace StrongSilver
open Real
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
set_option maxHeartbeats 1400000

theorem terminal_base_path {μ A : ℝ} (hμ : 0 ≤ μ) (hcap : μ*A ≤ 1/2) (t : List ℝ)
    (ht : ∀ b ∈ t, 0 < b → b ≤ A) {Y : V} (hY : Y ≠ 0) :
    ∃ Q : SupportedPath V μ t.length, List.ofFn Q.steps = t ∧ Q.x 0 = Y ∧ Q.x 0 ≠ 0 ∧
      Q.family.PositiveAt (Q.x 0) ∧ (∀ η : ℝ, Q.family.Gate (Q.x 0) η) ∧
      (∀ j, |inner ℝ (unitDirection (Q.x 0)) (Q.family.z j)| ≤ maxPrefixProduct μ t*‖Q.x 0‖ ∧
        |inner ℝ (unitDirection (Q.x 0)) (Q.family.g j)| ≤ 0*‖Q.x 0‖) ∧
      Real.exp (-4*(μ*Scalar.SignedIntervals.positiveMass t)) ≤ ‖Q.x (Fin.last _)‖^2/‖Q.x 0‖^2 := by
  have hsmall : ∀ b ∈ t, μ*b < 1 := by
    intro b hb
    by_cases hb0 : 0 < b
    · have hh := (mul_le_mul_of_nonneg_left (ht b hb hb0) hμ).trans hcap
      linarith only [hh]
    · have hh := mul_nonpos_of_nonneg_of_nonpos hμ (le_of_not_gt hb0)
      linarith only [hh]
  let Q := SupportedPath.quadraticRun μ t Y
  have hsource : Q.x 0 = Y := SupportedPath.quadraticRun_start μ t Y
  have hNZ : Q.x 0 ≠ 0 := by rwa [hsource]
  have hgain := SupportedPath.quadraticRun_terminal_gain hμ hcap t ht Y
  have hM := maxPrefixProduct_ge_one μ t
  have hV : 0 < ‖Y‖ := norm_pos_iff.mpr hY
  have hscale := mul_le_mul_of_nonneg_right hM (mul_nonneg (Real.exp_pos (-2*μ*Scalar.SignedIntervals.positiveMass t)).le hV.le)
  have hEnd : Real.exp (-2*μ*Scalar.SignedIntervals.positiveMass t)*‖Y‖ ≤ ‖Q.x (Fin.last _)‖ := by
    nlinarith only [hscale,hgain]
  have hEndSq := (sq_le_sq₀ (mul_nonneg (Real.exp_pos _).le hV.le) (norm_nonneg (Q.x (Fin.last _)))).mpr hEnd
  have hRatio : Real.exp (-4*(μ*Scalar.SignedIntervals.positiveMass t)) ≤ ‖Q.x (Fin.last _)‖^2/‖Q.x 0‖^2 := by
    rw [hsource]
    apply (le_div_iff₀ (sq_pos_of_pos hV)).mpr
    have he : Real.exp (-4*(μ*Scalar.SignedIntervals.positiveMass t)) = (Real.exp (-2*μ*Scalar.SignedIntervals.positiveMass t))^2 := by
      rw [pow_two,← Real.exp_add]
      congr 1
      ring
    rw [he]
    simpa only [mul_pow] using hEndSq
  refine ⟨Q,List.ofFn_get _,hsource,hNZ,?_,?_,?_,hRatio⟩
  · rw [hsource]
    exact SupportedPath.quadraticRun_positive t hsmall Y
  · intro η
    rw [hsource]
    exact SupportedPath.quadraticRun_gate μ t Y η
  · intro j
    rw [hsource]
    constructor
    · exact SupportedPath.quadraticRun_directional_bound t hsmall hY j
    · change |inner ℝ (unitDirection Y) ((SupportedPath.quadraticRun μ t Y).family.g j)| ≤ _
      rw [SupportedPath.quadraticRun_slope,inner_zero_right,abs_zero,zero_mul]

end
end StrongSilver
