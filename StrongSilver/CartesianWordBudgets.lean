-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CartesianProductTimeShape
import StrongSilver.FourPhaseWordMassBudget
import StrongSilver.FourPhaseReference

namespace StrongSilver.ScheduleTree.FourGapGroup
open FourPhase Scalar.SignedIntervals
noncomputable section
set_option maxHeartbeats 2800000

theorem phaseMass_massShape (G : FourGapGroup) (φ : ℝ → ℝ) (T : ℝ) (i : Fin 4) :
    phaseMass (G.massShape φ T) i = (prefixMax ((G.gaps i).map φ)+1)/T := by
  fin_cases i <;> rfl

theorem phaseExcess_massShape (G : FourGapGroup) (φ : ℝ → ℝ) (T : ℝ) (i : Fin 3) :
    phaseExcess (G.massShape φ T) i = G.internalExcesses φ i/T := by
  fin_cases i <;> rfl

theorem reference_mass (i : Fin 4) : phaseMass reference i = 1 := by fin_cases i <;> rfl

theorem reference_excess_le_one (i : Fin 3) : phaseExcess reference i ≤ 1 := by
  have hr : rho⁻¹ < 1 := by rw [rho_inv_identity]; linarith only [rho_bounds.2]
  fin_cases i
  · exact hr.le
  · exact le_rfl
  · exact hr.le

theorem internalExcesses_pivot_identity (G : FourGapGroup) (φ : ℝ → ℝ)
    (hKL : 0 < adjustedExcess φ G.first G.leftPivot) (i : Fin 3) :
    φ (G.pivots 0 i.castSucc) = G.internalExcesses φ i+1+drawdown ((G.gaps i.castSucc).map φ) := by
  have hd := (positive_excess_mass_identity φ G.first G.second G.leftPivot hKL).2
  change G.left.gapDrawdown φ = G.second.gapDrawdown φ at hd
  fin_cases i
  · change φ G.leftPivot = (φ G.leftPivot-1-G.first.gapDrawdown φ)+1+G.first.gapDrawdown φ
    ring
  · change φ G.middlePivot = (φ G.middlePivot-1-G.left.gapDrawdown φ)+1+G.second.gapDrawdown φ
    rw [hd]
    ring
  · change φ G.rightPivot = (φ G.rightPivot-1-G.third.gapDrawdown φ)+1+G.third.gapDrawdown φ
    ring

theorem pivots_internal_independent (G : FourGapGroup) (b : ℝ) (i : Fin 3) :
    G.pivots b i.castSucc = G.pivots 0 i.castSucc := by fin_cases i <;> rfl

/-- All actual step and duration budgets used in the four-phase error
estimates follow from the mass shape and the actual negative mass.
No actual absolute-mass budget is left as a separate hypothesis. -/
theorem massShape_word_budgets (G : FourGapGroup) {μ T b : ℝ}
    (hμ : 0 < μ) (hT : 1 ≤ T)
    (hsteps : ∀ i, ∀ s ∈ G.gaps i, μ*s < 1)
    (hpivot : ∀ i : Fin 3, 0 < G.pivots b i.castSucc ∧ μ*G.pivots b i.castSucc < 1)
    (hKL : 0 < adjustedExcess (logarithmicStep μ) G.first G.leftPivot)
    (hnear : ∀ j, |G.massShape (logarithmicStep μ) T j-reference j| ≤ 1/2)
    (hnegative : ∀ i, negativeMass (G.gaps i) ≤ T)
    (hscale : μ*T ≤ 1/400) :
    (∀ i, transformedGapMaximum μ (G.gaps i)+1 ≤ 100*T) ∧
    absoluteMass (boundedWord G.gaps (G.pivots b)) ≤ 100*T ∧
    μ*absoluteMass (boundedWord G.gaps (G.pivots b)) ≤ 1/4 ∧ μ*(100*T) ≤ 1 ∧
    (∀ i, |phaseDuration μ G.gaps (G.pivots b) i| ≤ 100*T) := by
  have hTpos := zero_lt_one.trans_le hT
  have hm (i : Fin 4) : transformedGapMaximum μ (G.gaps i)+1 ≤ 2*T := by
    have he := transformed_prefix_max hμ (G.gaps i) (hsteps i)
    change prefixMax ((G.gaps i).map (logarithmicStep μ)) = transformedGapMaximum μ (G.gaps i) at he
    have hc := (abs_le.mp (hnear (i.castLE (by decide : 4 ≤ 8)))).2
    change phaseMass (G.massShape (logarithmicStep μ) T) i-phaseMass reference i ≤ 1/2 at hc
    rw [G.phaseMass_massShape,reference_mass,he] at hc
    exact (div_le_iff₀ hTpos).mp (by linarith only [hc])
  have hk (i : Fin 3) : G.internalExcesses (logarithmicStep μ) i ≤ 2*T := by
    have hc := (abs_le.mp (hnear ⟨i.val+4,by omega⟩)).2
    change phaseExcess (G.massShape (logarithmicStep μ) T) i-phaseExcess reference i ≤ 1/2 at hc
    rw [G.phaseExcess_massShape] at hc
    have hr := reference_excess_le_one i
    exact (div_le_iff₀ hTpos).mp (by linarith only [hc,hr])
  have hp (i : Fin 3) : |G.pivots b i.castSucc| ≤ 4*T ∧
      0 ≤ logarithmicStep μ (G.pivots b i.castSucc) ∧
      logarithmicStep μ (G.pivots b i.castSucc) ≤ 4*T := by
    have hφpos := logarithmicStep_pos hμ (hpivot i).1 (hpivot i).2
    have hφge := logarithmicStep_ge hμ (hpivot i).2
    have he := G.internalExcesses_pivot_identity (logarithmicStep μ) hKL i
    rw [← G.pivots_internal_independent b i] at he
    have hd := (transformed_drawdown_le_negative_mass hμ (G.gaps i.castSucc) (hsteps i.castSucc)).trans (hnegative i.castSucc)
    have hb : logarithmicStep μ (G.pivots b i.castSucc) ≤ 4*T := by linarith only [he,hk i,hd,hT]
    exact ⟨by rw [abs_of_pos (hpivot i).1]; exact hφge.trans hb,hφpos.le,hb⟩
  have hbudget := four_phase_word_budgets hμ hTpos.le G.gaps (G.pivots b) hsteps hm hnegative hp hscale
  refine ⟨fun i => (hm i).trans (by linarith only [hT]),hbudget⟩

end
end StrongSilver.ScheduleTree.FourGapGroup
