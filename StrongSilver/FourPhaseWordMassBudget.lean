-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.TransformedActualMass
import StrongSilver.FourPhaseWordTimeError

namespace StrongSilver.FourPhase
open Scalar.SignedIntervals
noncomputable section
set_option maxHeartbeats 2200000

/-- Actual absolute mass on each original signed gap is O(T) whenever
the transformed prefix mass is O(T) and the actual negative mass is O(T). -/
theorem gap_absolute_mass_budget {μ T : ℝ} (hμ : 0 < μ) (hT : 0 ≤ T)
    (gap : Fin 4 → List ℝ)
    (hsteps : ∀ i, ∀ b ∈ gap i, μ*b < 1)
    (hmass : ∀ i, transformedGapMaximum μ (gap i)+1 ≤ 2*T)
    (hnegative : ∀ i, negativeMass (gap i) ≤ T) :
    ∀ i, absoluteMass (gap i) ≤ 4*T := by
  intro i
  have h := absolute_mass_le_transformed_prefix hμ (gap i) (hsteps i)
  linarith only [h,hmass i,hnegative i]

theorem bounded_word_mass_budget {T : ℝ} (hT : 0 ≤ T)
    (gap : Fin 4 → List ℝ) (pivot : Fin 4 → ℝ)
    (hgap : ∀ i, absoluteMass (gap i) ≤ 4*T)
    (hpivot : ∀ i : Fin 3, |pivot i.castSucc| ≤ 4*T) :
    absoluteMass (boundedWord gap pivot) ≤ 100*T := by
  have hs (b : ℝ) : absoluteMass [b] = |b| := by simp [absoluteMass]
  simp only [boundedWord,phaseWord,absoluteMass_append,hs]
  have h0 := hgap 0
  have h1 := hgap 1
  have h2 := hgap 2
  have h3 := hgap 3
  have hp0 := hpivot 0
  have hp1 := hpivot 1
  have hp2 := hpivot 2
  change |pivot 0| ≤ 4*T at hp0
  change |pivot 1| ≤ 4*T at hp1
  change |pivot 2| ≤ 4*T at hp2
  linarith only [h0,h1,h2,h3,hp0,hp1,hp2,hT]

theorem phase_duration_mass_budget {μ T : ℝ} (hμ : 0 < μ) (hT : 0 ≤ T)
    (gap : Fin 4 → List ℝ) (pivot : Fin 4 → ℝ)
    (hsteps : ∀ i, ∀ b ∈ gap i, μ*b < 1)
    (hmass : ∀ i, transformedGapMaximum μ (gap i)+1 ≤ 2*T)
    (hnegative : ∀ i, negativeMass (gap i) ≤ T)
    (hpivot : ∀ i : Fin 3, 0 ≤ logarithmicStep μ (pivot i.castSucc) ∧
      logarithmicStep μ (pivot i.castSucc) ≤ 4*T) :
    ∀ i, |phaseDuration μ gap pivot i| ≤ 100*T := by
  intro i
  have hm := transformedGapMaximum_nonnegative hμ (gap i.castSucc) (hsteps i.castSucc)
  have hd := drawdown_nonneg ((gap i.castSucc).map (logarithmicStep μ))
  have hdb := (transformed_drawdown_le_negative_mass hμ (gap i.castSucc) (hsteps i.castSucc)).trans (hnegative i.castSucc)
  have he : phaseDuration μ gap pivot i = transformedGapMaximum μ (gap i.castSucc)-
      drawdown ((gap i.castSucc).map (logarithmicStep μ))+logarithmicStep μ (pivot i.castSucc) := by
    have ht := transformed_prefix_max hμ (gap i.castSucc) (hsteps i.castSucc)
    change prefixMax ((gap i.castSucc).map (logarithmicStep μ)) = transformedGapMaximum μ (gap i.castSucc) at ht
    simp only [phaseDuration,phaseWord,List.map_append,List.sum_append,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,drawdown,ht]
    ring
  rw [he]
  exact abs_le.mpr ⟨by linarith only [hm,hdb,(hpivot i).1,hT],
    by linarith only [hmass i.castSucc,hd,(hpivot i).2,hT]⟩

/-- The product smallness used in the local construction follows from
these actual mass estimates and the single condition mu*T <= 1/400. -/
theorem four_phase_word_budgets {μ T : ℝ} (hμ : 0 < μ) (hT : 0 ≤ T)
    (gap : Fin 4 → List ℝ) (pivot : Fin 4 → ℝ)
    (hsteps : ∀ i, ∀ b ∈ gap i, μ*b < 1)
    (hmass : ∀ i, transformedGapMaximum μ (gap i)+1 ≤ 2*T)
    (hnegative : ∀ i, negativeMass (gap i) ≤ T)
    (hpivot : ∀ i : Fin 3, |pivot i.castSucc| ≤ 4*T ∧
      0 ≤ logarithmicStep μ (pivot i.castSucc) ∧ logarithmicStep μ (pivot i.castSucc) ≤ 4*T)
    (hscale : μ*T ≤ 1/400) :
    absoluteMass (boundedWord gap pivot) ≤ 100*T ∧
    μ*absoluteMass (boundedWord gap pivot) ≤ 1/4 ∧ μ*(100*T) ≤ 1 ∧
    (∀ i, |phaseDuration μ gap pivot i| ≤ 100*T) := by
  have hab := bounded_word_mass_budget hT gap pivot
    (gap_absolute_mass_budget hμ hT gap hsteps hmass hnegative) (fun i => (hpivot i).1)
  have hmul := mul_le_mul_of_nonneg_left hab hμ.le
  refine ⟨hab,by nlinarith only [hmul,hscale],by nlinarith only [hscale],?_⟩
  exact phase_duration_mass_budget hμ hT gap pivot hsteps hmass hnegative (fun i => (hpivot i).2)

end
end StrongSilver.FourPhase
