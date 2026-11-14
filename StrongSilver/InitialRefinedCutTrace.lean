-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.InitialAssemblyValidation
import StrongSilver.InitialRefinedParameters

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 1800000

theorem InitialCutAssembly.tracked_good {good : CutPhase → Bool} {s : InitialCutAssembly} (hs : s.WellFormed good) :
    ∀ q ∈ s.trackedPhases, good q = true := by
  induction s with
  | terminal => simp [trackedPhases]
  | tracked q s ih =>
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hs.1
    · exact ih hs.2 z hz
  | block q I c d s ih => exact ih hs.2.2.2
  | terminalBlock q I c => simp [trackedPhases]
  | noConnector q I => simp [trackedPhases]

def initialPhaseGood (κ B μ T : ℝ) (q : CutPhase) : Bool :=
  @decide (InitialPhaseBudget B μ q.pivot T κ B q.gap) (Classical.propDecidable _)

/-- Exact refined-cut realization when the first phase is good. Tracked
ordinary parameters and all word-preservation obligations are discharged
from the original initial budgets and the threshold selector. -/
theorem eventually_initial_good_first_refined_cut : ∀ᶠ A : ℝ in atTop,
    ∀ κ B μ T P : ℝ, ∀ choose : ℕ → ℝ → Bool, ∀ q : CutPhase, ∀ qs : List CutPhase, ∀ t : List ℝ,
      A ≤ B → 2 ≤ B → κ ≤ A^((1003 : ℝ)/1000) →
      1 ≤ κ → 1/κ ≤ μ → μ ≤ 1 → μ*B ≤ 1/2 →
      A^((49 : ℝ)/50) ≤ P → P ≤ A^((199 : ℝ)/200) →
      (∀ i b, choose i b = true → A ≤ b) → (∀ i b, choose i b = false → 0 < b → b ≤ A) →
      initialPhaseGood κ B μ T q = true →
      (∀ a ∈ t, 0 < a → a ≤ B) → (∀ a ∈ (q::qs).flatMap CutPhase.word++t, 1-μ*a ≠ 0) →
      ∃ s : InitialCutAssembly, s.phases = q::qs ∧ s.WellFormed (initialPhaseGood κ B μ T) ∧
        s.reserved.length ≤ 7*badPhaseCount (initialPhaseGood κ B μ T) (q::qs) ∧
        ENNReal.ofReal (s.rate A κ B μ P (refinePhase choose) t) ≤ D κ ((q::qs).flatMap CutPhase.word++t) := by
  classical
  filter_upwards [eventually_initial_refined_parameters,InitialCutAssembly.eventually_original_word_distance_lower]
    with A hparams hlower
  intro κ B μ T P choose q qs t hAB hB hκA hκ hμ hμ1 hcap hPL hPU hselected hunselected hq ht hcritical
  let good := initialPhaseGood κ B μ T
  have hW : ∀ z, good z = true → InitialPhaseBudget B μ z.pivot T κ B z.gap := fun _ hz => of_decide_eq_true hz
  obtain ⟨s,hph,hs,hc⟩ := exists_initial_cutAssembly good q qs hq
  have hr : ∀ z ∈ s.trackedPhases, (refinePhase choose z).flatMap CutPhase.word = z.word := fun z _ => refinePhase_word choose z
  have ho : ∀ z ∈ s.trackedPhases, ∀ w ∈ refinePhase choose z, OrdinaryPhaseParameters A μ w.pivot T P w.gap := by
    intro z hz
    exact hparams κ B μ T P z choose hAB hκA hPL hPU (hW z (s.tracked_good hs z hz)) hselected hunselected
  have hcrit' : ∀ a ∈ s.phases.flatMap CutPhase.word++t, 1-μ*a ≠ 0 := by simpa only [hph] using hcritical
  refine ⟨s,hph,hs,?_,?_⟩
  · simpa only [hph] using s.reserved_count_bound hs hc
  · simpa only [hph] using hlower κ B μ T P good hW s hs (refinePhase choose) hr ho t hAB hB hκA hκ hμ hμ1 hcap ht hcrit'

end
end StrongSilver
