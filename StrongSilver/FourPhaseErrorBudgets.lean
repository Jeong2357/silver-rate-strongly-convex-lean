-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseExcessTimeError

namespace StrongSilver.FourPhase
noncomputable section
set_option maxHeartbeats 1800000

theorem mass_error_budget_scaled {μ K T m N : ℝ} (hμ : 0 ≤ μ) (hK : 1 ≤ K) (hT : 1 ≤ T)
    (hm : 0 ≤ m) (hN : 0 ≤ N) (hmT : m+1 ≤ K*T) (hNT : N ≤ K*T) :
    2*μ*m^2+4*μ*N*(m+1) ≤ 6*K^2*μ*T^2 := by
  have hKT : 0 ≤ K*T := mul_nonneg (zero_le_one.trans hK) (zero_le_one.trans hT)
  have hm0 : m ≤ K*T := by linarith only [hmT]
  have hsq : m^2 ≤ (K*T)^2 := by nlinarith only [hm0,hm,hKT]
  have hprod := mul_le_mul hNT hmT (show 0 ≤ m+1 by linarith only [hm]) hKT
  have h1 := mul_le_mul_of_nonneg_left hsq hμ
  have h2 := mul_le_mul_of_nonneg_left hprod hμ
  nlinarith only [h1,h2]

theorem time_error_budget_scaled {μ K T s N : ℝ} (hμ : 0 ≤ μ) (hK : 1 ≤ K) (hT : 1 ≤ T)
    (hN : 0 ≤ N) (hsT : |s| ≤ K*T) (hNT : N ≤ K*T) :
    2*μ*s^2+(4*μ*N+2*μ)*|s| ≤ (6*K^2+2*K)*μ*T^2 := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  have hKT : 0 ≤ K*T := mul_nonneg hK0 hT0
  have hsq : s^2 ≤ (K*T)^2 := by nlinarith only [hsT,abs_nonneg s,sq_abs s,hKT]
  have hprod := mul_le_mul hNT hsT (abs_nonneg s) hKT
  have hTT : T ≤ T^2 := by nlinarith only [hT]
  have hKT2 := mul_le_mul_of_nonneg_left hTT hK0
  have habs : |s| ≤ K*T^2 := hsT.trans hKT2
  have h1 := mul_le_mul_of_nonneg_left hsq hμ
  have h2 := mul_le_mul_of_nonneg_left hprod hμ
  have h3 := mul_le_mul_of_nonneg_left habs hμ
  nlinarith only [h1,h2,h3]

/-- Both exact product-time budgets are bounded by an absolute multiple
of mu*T^2 once the actual masses and durations are on scale T. -/
theorem actual_error_budgets_scaled {μ K T : ℝ} (hμ : 0 < μ) (hK : 1 ≤ K) (hT : 1 ≤ T)
    (gap : Fin 4 → List ℝ) (pivot : Fin 4 → ℝ)
    (hsmall : μ*absoluteMass (boundedWord gap pivot) ≤ 1/4) (i : Fin 3)
    (hm : transformedGapMaximum μ (gap i.castSucc)+1 ≤ K*T)
    (hs : |phaseDuration μ gap pivot i| ≤ K*T)
    (hN : absoluteMass (boundedWord gap pivot) ≤ K*T) :
    massErrorBudget μ gap pivot i.castSucc+timeErrorBudget μ gap pivot i ≤
      (12*K^2+2*K)*μ*T^2 := by
  have hm0 := transformedGapMaximum_nonnegative hμ (gap i.castSucc) (gap_small_steps hμ.le gap pivot hsmall i.castSucc)
  have hN0 := absoluteMass_nonnegative (boundedWord gap pivot)
  have h1 := mass_error_budget_scaled hμ.le hK hT hm0 hN0 hm hN
  have h2 := time_error_budget_scaled hμ.le hK hT hN0 hs hN
  unfold massErrorBudget timeErrorBudget
  nlinarith only [h1,h2]

end
end StrongSilver.FourPhase
