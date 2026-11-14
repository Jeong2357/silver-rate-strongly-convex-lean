-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseMassTimeError
import StrongSilver.DiscountedExpQuotientError

namespace StrongSilver.FourPhase
noncomputable section
set_option maxHeartbeats 2600000

theorem firstWord_sublist_bounded (gap : Fin 4 → List ℝ) (pivot : Fin 4 → ℝ) (i : Fin 3) :
    (phaseWord gap pivot i.castSucc).Sublist (boundedWord gap pivot) := by
  unfold boundedWord
  simp only [List.append_assoc]
  fin_cases i
  · exact List.sublist_append_left _ _
  · exact (List.sublist_append_left _ _).trans (List.sublist_append_right _ _)
  · exact (List.sublist_append_left _ _).trans
      ((List.sublist_append_right _ _).trans (List.sublist_append_right _ _))

theorem firstWord_small_steps {μ : ℝ} (hμ : 0 ≤ μ) (gap : Fin 4 → List ℝ) (pivot : Fin 4 → ℝ)
    (hsmall : μ*absoluteMass (boundedWord gap pivot) ≤ 1/4) (i : Fin 3) :
    ∀ b ∈ phaseWord gap pivot i.castSucc, μ*b < 1 := by
  have hh := small_absolute_mass_steps hμ (boundedWord gap pivot) (show μ*absoluteMass (boundedWord gap pivot) ≤ 1/2 by linarith only [hsmall])
  exact fun b hb => hh b ((firstWord_sublist_bounded gap pivot i).subset hb)

theorem inverse_product_eq_exp_logarithmic_sum {μ : ℝ} (hμ : 0 < μ) (h : List ℝ)
    (hh : ∀ b ∈ h, μ*b < 1) :
    (quadraticMultiplier μ h)⁻¹ = Real.exp (μ*(h.map (logarithmicStep μ)).sum) := by
  rw [logarithmicSteps_sum h hh]
  have he : μ*(-Real.log (quadraticMultiplier μ h)/μ) = -Real.log (quadraticMultiplier μ h) :=
    mul_div_cancel₀ _ hμ.ne'
  rw [he,Real.exp_neg,Real.exp_log (quadraticMultiplier_positive h hh)]

def phaseDuration (μ : ℝ) (gap : Fin 4 → List ℝ) (pivot : Fin 4 → ℝ) (i : Fin 3) : ℝ :=
  ((phaseWord gap pivot i.castSucc).map (logarithmicStep μ)).sum

theorem normalized_time_formula {μ T : ℝ} (hμ : 0 < μ) (hT : 0 < T)
    (gap : Fin 4 → List ℝ) (pivot : Fin 4 → ℝ)
    (hsmall : μ*absoluteMass (boundedWord gap pivot) ≤ 1/4) (ζ : ℝ) (i : Fin 3) :
    T*phaseTime (productShape μ T gap pivot ζ) i =
      ((1-μ)/carry μ gap pivot i.castSucc)*((Real.exp (μ*phaseDuration μ gap pivot i)-1)/μ) := by
  have hC := (carry_positive hμ.le gap pivot hsmall i.castSucc).ne'
  have hp := (first_phase_product_positive hμ.le gap pivot hsmall i).ne'
  have hinv := inverse_product_eq_exp_logarithmic_sum hμ (phaseWord gap pivot i.castSucc)
    (firstWord_small_steps hμ.le gap pivot hsmall i)
  have hcancel : T*phaseTime (productShape μ T gap pivot ζ) i =
      ((1-μ)/carry μ gap pivot i.castSucc)*(((quadraticMultiplier μ (phaseWord gap pivot i.castSucc))⁻¹-1)/μ) := by
    rw [phaseTime_eq,productShape_mass,productShape_excess]
    unfold normalizedExcess
    rw [carry_recurrence]
    field_simp [hμ.ne',hT.ne',hC,hp]
    <;> ring
  rw [hcancel,hinv]
  rfl

theorem actual_normalized_time_error {μ T : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1) (hT : 0 < T)
    (gap : Fin 4 → List ℝ) (pivot : Fin 4 → ℝ)
    (hsmall : μ*absoluteMass (boundedWord gap pivot) ≤ 1/4) (ζ : ℝ) (i : Fin 3)
    (hphase : |μ*phaseDuration μ gap pivot i| ≤ 1) :
    |T*phaseTime (productShape μ T gap pivot ζ) i-phaseDuration μ gap pivot i| ≤
      2*μ*(phaseDuration μ gap pivot i)^2+
      (4*μ*absoluteMass (boundedWord gap pivot)+2*μ)*|phaseDuration μ gap pivot i| := by
  have hC := (carry_prefix_bounds hμ.le gap pivot hsmall i.castSucc 0).1
  have hnil : quadraticMultiplier μ ((gap i.castSucc).take 0) = 1 := rfl
  rw [hnil,mul_one] at hC
  rw [normalized_time_formula hμ hT gap pivot hsmall]
  have he := discounted_exp_quotient_error hμ hμ1 hC hphase
  have hc := carry_deviation hμ.le gap pivot hsmall i.castSucc
  have hprice := mul_le_mul_of_nonneg_right hc (abs_nonneg (phaseDuration μ gap pivot i))
  nlinarith only [he,hprice]

end
end StrongSilver.FourPhase
