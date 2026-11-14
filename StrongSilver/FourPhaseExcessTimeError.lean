-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseWordTimeError

namespace StrongSilver.FourPhase
noncomputable section
set_option maxHeartbeats 2200000

def massErrorBudget (μ : ℝ) (gap : Fin 4 → List ℝ) (pivot : Fin 4 → ℝ) (i : Fin 4) : ℝ :=
  2*μ*(transformedGapMaximum μ (gap i))^2+
    4*μ*absoluteMass (boundedWord gap pivot)*(transformedGapMaximum μ (gap i)+1)

def timeErrorBudget (μ : ℝ) (gap : Fin 4 → List ℝ) (pivot : Fin 4 → ℝ) (i : Fin 3) : ℝ :=
  2*μ*(phaseDuration μ gap pivot i)^2+
    (4*μ*absoluteMass (boundedWord gap pivot)+2*μ)*|phaseDuration μ gap pivot i|

theorem actual_normalized_excess_error {μ T : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1) (hT : 0 < T)
    (gap : Fin 4 → List ℝ) (pivot : Fin 4 → ℝ)
    (hsmall : μ*absoluteMass (boundedWord gap pivot) ≤ 1/4) (ζ : ℝ) (i : Fin 3)
    (hgap : μ*transformedGapMaximum μ (gap i.castSucc) ≤ 1)
    (hphase : |μ*phaseDuration μ gap pivot i| ≤ 1) :
    |T*normalizedExcess μ T gap pivot i-
      (phaseDuration μ gap pivot i-(transformedGapMaximum μ (gap i.castSucc)+1))| ≤
      massErrorBudget μ gap pivot i.castSucc+timeErrorBudget μ gap pivot i := by
  have hm := actual_normalized_mass_error hμ hT gap pivot hsmall i.castSucc hgap
  have ht := actual_normalized_time_error hμ hμ1 hT gap pivot hsmall ζ i hphase
  have he : T*normalizedExcess μ T gap pivot i-
      (phaseDuration μ gap pivot i-(transformedGapMaximum μ (gap i.castSucc)+1)) =
      (T*phaseTime (productShape μ T gap pivot ζ) i-phaseDuration μ gap pivot i)-
      (T*normalizedMass μ T gap pivot i.castSucc-(transformedGapMaximum μ (gap i.castSucc)+1)) := by
    rw [phaseTime_eq,productShape_mass,productShape_excess]
    ring
  have htriangle := abs_add_le
    (T*phaseTime (productShape μ T gap pivot ζ) i-phaseDuration μ gap pivot i)
    (-(T*normalizedMass μ T gap pivot i.castSucc-(transformedGapMaximum μ (gap i.castSucc)+1)))
  rw [abs_neg] at htriangle
  rw [he,sub_eq_add_neg]
  unfold massErrorBudget timeErrorBudget
  nlinarith only [htriangle,hm,ht]

/-- The unperturbed internal excess uses the original transformed pivot
and the drawdown of its preceding actual gap. -/
theorem phaseDuration_minus_mass {μ : ℝ} (hμ : 0 < μ)
    (gap : Fin 4 → List ℝ) (pivot : Fin 4 → ℝ)
    (hsmall : μ*absoluteMass (boundedWord gap pivot) ≤ 1/4) (i : Fin 3) :
    phaseDuration μ gap pivot i-(transformedGapMaximum μ (gap i.castSucc)+1) =
      logarithmicStep μ (pivot i.castSucc)-1-
        Scalar.SignedIntervals.drawdown ((gap i.castSucc).map (logarithmicStep μ)) := by
  have hm := transformed_prefix_max hμ (gap i.castSucc) (gap_small_steps hμ.le gap pivot hsmall i.castSucc)
  change Scalar.SignedIntervals.prefixMax ((gap i.castSucc).map (logarithmicStep μ)) =
    transformedGapMaximum μ (gap i.castSucc) at hm
  simp only [phaseDuration,phaseWord,List.map_append,List.sum_append,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Scalar.SignedIntervals.drawdown]
  linarith only [hm]

end
end StrongSilver.FourPhase
