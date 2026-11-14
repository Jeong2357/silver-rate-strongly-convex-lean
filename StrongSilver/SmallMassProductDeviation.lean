-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseWords

namespace StrongSilver
open Scalar.SignedIntervals
noncomputable section
set_option maxHeartbeats 1800000

theorem small_absolute_mass_product_deviation {μ : ℝ} (hμ : 0 ≤ μ) (h : List ℝ)
    (hsmall : μ*absoluteMass h ≤ 1/4) : |quadraticMultiplier μ h-1| ≤ 2*μ*absoluteMass h := by
  have hmass := mul_nonneg hμ (absoluteMass_nonnegative h)
  have hlo := small_absolute_mass_product_lower hμ h (show μ*absoluteMass h ≤ 1/2 by linarith only [hsmall])
  have hN := mul_le_mul_of_nonneg_left (negativeMass_le_absoluteMass h) hμ
  have hn := mul_nonneg hμ (negativeMass_nonnegative h)
  have hcharge : μ*negativeMass h ≤ 1 := by linarith only [hN,hsmall]
  have hq := quadraticMultiplier_le_exp_negative_mass hμ h
    (small_absolute_mass_steps hμ h (by linarith only [hsmall]))
  have he := Real.abs_exp_sub_one_le (x := μ*negativeMass h) (by rw [abs_of_nonneg hn]; exact hcharge)
  rw [abs_of_nonneg hn] at he
  have heupper := le_abs_self (Real.exp (μ*negativeMass h)-1)
  apply abs_le.mpr
  constructor <;> nlinarith only [hmass,hlo,hN,hq,he,heupper]

namespace FourPhase

theorem carry_deviation {μ : ℝ} (hμ : 0 ≤ μ) (gap : Fin 4 → List ℝ) (pivot : Fin 4 → ℝ)
    (hsmall : μ*absoluteMass (boundedWord gap pivot) ≤ 1/4) (i : Fin 4) :
    |carry μ gap pivot i-1| ≤ 2*μ*absoluteMass (boundedWord gap pivot) := by
  have hsub : (priorWord gap pivot i).Sublist (boundedWord gap pivot) :=
    (List.sublist_append_left _ _).trans (prior_gap_sublist_bounded gap pivot i)
  have hm := mul_le_mul_of_nonneg_left (absoluteMass_sublist_le hsub) hμ
  have hh := small_absolute_mass_product_deviation hμ (priorWord gap pivot i) (hm.trans hsmall)
  change |carry μ gap pivot i-1| ≤ _ at hh
  nlinarith only [hh,hm]

end FourPhase
end
end StrongSilver
