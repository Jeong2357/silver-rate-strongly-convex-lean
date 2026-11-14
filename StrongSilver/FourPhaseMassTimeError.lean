-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseProductShape
import StrongSilver.ExpQuotientError
import StrongSilver.SmallMassProductDeviation
import StrongSilver.PlanarGapNorm

namespace StrongSilver.FourPhase
noncomputable section
set_option maxHeartbeats 2400000

theorem queryTime_mass_error {μ T C m α : ℝ} (hμ : 0 < μ) (hT : 0 < T)
    (hC : 1/2 ≤ C) (hm : 0 ≤ m) (hsmall : μ*m ≤ 1)
    (hα : α⁻¹ = Real.exp (μ*m)) :
    |T*queryTime μ T C α-(m+1)| ≤ 2*μ*m^2+2*|C-1| *(m+1) := by
  have hCp : 0 < C := by linarith only [hC]
  have hq : 0 ≤ m+1 := by linarith only [hm]
  let a := (Real.exp (μ*m)-1)/μ+1
  have ha : |a-(m+1)| ≤ μ*m^2 := by
    have hh := exp_quotient_error hμ (show |μ*m| ≤ 1 by rw [abs_of_nonneg (mul_nonneg hμ.le hm)]; exact hsmall)
    have he : a-(m+1) = (Real.exp (μ*m)-1)/μ-m := by dsimp [a]; ring
    rwa [he]
  have htime : T*queryTime μ T C α = a/C := by
    unfold queryTime
    rw [hα]
    dsimp [a]
    field_simp
    <;> ring
  have he : a/C-(m+1) = (a-(m+1))/C+(C⁻¹-1)*(m+1) := by
    field_simp
    <;> ring
  have hfirst : |(a-(m+1))/C| ≤ 2*μ*m^2 := by
    rw [abs_div,abs_of_pos hCp]
    apply (div_le_iff₀ hCp).mpr
    have hp := mul_le_mul_of_nonneg_left hC (mul_nonneg hμ.le (sq_nonneg m))
    nlinarith only [ha,hp]
  have hsecond : |(C⁻¹-1)*(m+1)| ≤ 2*|C-1| *(m+1) := by
    rw [abs_mul,abs_of_nonneg hq]
    exact mul_le_mul_of_nonneg_right (inverse_deviation_half hC) hq
  rw [htime,he]
  exact (abs_add_le _ _).trans (add_le_add hfirst hsecond)

/-- Exact normalized masses from actual signed schedule products are
compared with the transformed gap masses, including the offset one. -/
theorem actual_normalized_mass_error {μ T : ℝ} (hμ : 0 < μ) (hT : 0 < T)
    (gap : Fin 4 → List ℝ) (pivot : Fin 4 → ℝ)
    (hsmall : μ*absoluteMass (boundedWord gap pivot) ≤ 1/4) (i : Fin 4)
    (hgap : μ*transformedGapMaximum μ (gap i) ≤ 1) :
    |T*normalizedMass μ T gap pivot i-(transformedGapMaximum μ (gap i)+1)| ≤
      2*μ*(transformedGapMaximum μ (gap i))^2+
      4*μ*absoluteMass (boundedWord gap pivot)*(transformedGapMaximum μ (gap i)+1) := by
  have hh := gap_small_steps hμ.le gap pivot hsmall i
  have hm := transformedGapMaximum_nonnegative hμ (gap i) hh
  have hα := (transformedGapMaximum_exp hμ (gap i) hh).symm
  have hC := (carry_prefix_bounds hμ.le gap pivot hsmall i 0).1
  have hnil : quadraticMultiplier μ ((gap i).take 0) = 1 := rfl
  rw [hnil,mul_one] at hC
  have hmass := queryTime_mass_error hμ hT hC hm hgap hα
  have hdev := carry_deviation hμ.le gap pivot hsmall i
  have hprice := mul_le_mul_of_nonneg_right hdev (show 0 ≤ transformedGapMaximum μ (gap i)+1 by linarith only [hm])
  change |T*normalizedMass μ T gap pivot i-(transformedGapMaximum μ (gap i)+1)| ≤ _ at hmass
  nlinarith only [hmass,hprice]

end
end StrongSilver.FourPhase
