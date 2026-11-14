-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.NormalizedQuadratic

namespace StrongSilver
open Real
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [ProperSpace V]
set_option maxHeartbeats 1800000

theorem normalized_terminal_path {μ A : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1) (hcap : μ*A ≤ 1/2)
    (I t : List ℝ) (hcritical : ∀ b ∈ I, 1-μ*b ≠ 0) (ht : ∀ b ∈ t, 0 < b → b ≤ A)
    {Y : V} (hY : Y ≠ 0) :
    ∃ Q : SupportedPath V μ (I++t).length,
      List.ofFn Q.steps = I++t ∧ Q.x (Fin.last _) = Y ∧ Q.x 0 ≠ 0 ∧
      ‖Q.x 0‖ ≤ Real.exp (inverseCharge μ I+2*μ*Scalar.SignedIntervals.positiveMass t)*‖Y‖ ∧
      (∀ j, |inner ℝ (unitDirection (Q.x 0)) (Q.family.z j)| ≤
        Real.exp (inverseCharge μ I+2*μ*Scalar.SignedIntervals.positiveMass t)*‖Y‖) ∧
      (∀ j, Q.family.g j = 0) ∧ ∀ η : ℝ, Q.family.Gate (Q.x 0) η := by
  have htcritical : ∀ b ∈ t, 1-μ*b ≠ 0 := by
    intro b hb
    have hsmall : μ*b < 1 := by
      by_cases hb0 : 0 < b
      · have hh := (mul_le_mul_of_nonneg_left (ht b hb hb0) hμ.le).trans hcap
        linarith only [hh]
      · have hh := mul_nonpos_of_nonneg_of_nonpos hμ.le (le_of_not_gt hb0)
        linarith only [hh]
    linarith only [hsmall]
  have hall : ∀ b ∈ I++t, 1-μ*b ≠ 0 := by
    intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact hcritical b hb
    · exact htcritical b hb
  have hc := inverseCharge_small_steps hμ.le hcap t ht
  have hcharge : inverseCharge μ (I++t) ≤ inverseCharge μ I+2*μ*Scalar.SignedIntervals.positiveMass t := by
    rw [inverseCharge_append]
    linarith only [hc]
  have hbound := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hcharge) (norm_nonneg Y)
  let Q := normalizedQuadraticPath μ (I++t) Y
  refine ⟨Q,normalizedQuadraticPath_steps μ (I++t) Y,normalizedQuadraticPath_end (I++t) hall Y,
    normalizedQuadraticPath_ne_zero (I++t) hall hY,?_,?_,?_,?_⟩
  · exact (normalizedQuadraticPath_source_norm hμ hμ1 (I++t) hall Y).trans hbound
  · intro j
    exact (normalizedQuadraticPath_directional hμ hμ1 (I++t) hall hY j).trans hbound
  · exact normalizedQuadraticPath_slope μ (I++t) Y
  · exact normalizedQuadraticPath_gate μ (I++t) Y

end
end StrongSilver
