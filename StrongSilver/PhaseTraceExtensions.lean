-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.WorkingReplacement
import StrongSilver.OrdinaryCutTrace

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 3000000

/-- Original-word version of the retained-suffix extension interface,
used for a disjoint pair of phases or a refined ordinary run. -/
def WordTraceExtension (A μ : ℝ) (word : List ℝ) (factor : ℝ) : Prop :=
  ∀ h : List ℝ, ∀ M G r : ℝ, 0 ≤ r → PositiveTrace μ h (workingGateFraction A) M G r →
    Nonempty (PositiveTrace μ (word++h) (workingGateFraction A) (A^(10:ℝ)) (A^(10:ℝ)) (r*factor))

theorem eventually_ordinary_phase_extension : ∀ᶠ A : ℝ in atTop,
    ∀ μ T P : ℝ, ∀ q : CutPhase, OrdinaryPhaseParameters A μ q.pivot T P q.gap →
    PhaseTraceExtension A μ q ((ordinaryReferenceFactor A μ q.pivot P q.gap)^2) := by
  filter_upwards [eventually_ordinary_positive_trace] with A hattach
  intro μ T P q W h M G r hr S
  exact hattach μ q.pivot T P q.gap W h M G r S

/-- An arbitrary nonempty ordinary refinement extends the actual
retained suffix. Every refined original signed step is preserved. -/
theorem eventually_ordinary_run_extension : ∀ᶠ A : ℝ in atTop,
    ∀ μ T P : ℝ, ∀ qs : List CutPhase, qs ≠ [] →
    (∀ q ∈ qs, OrdinaryPhaseParameters A μ q.pivot T P q.gap) →
    WordTraceExtension A μ (qs.flatMap CutPhase.word) ((ordinaryPhaseProduct A μ P qs)^2) := by
  filter_upwards [eventually_ordinary_positive_trace] with A hattach
  intro μ T P qs
  induction qs with
  | nil => intro h; exact False.elim (h rfl)
  | cons q qs ih =>
    intro hnonempty hgood h M G r hr S
    have hq := hgood q (by simp)
    have htail : ∀ p ∈ qs, OrdinaryPhaseParameters A μ p.pivot T P p.gap :=
      fun p hp => hgood p (List.mem_cons_of_mem q hp)
    cases qs with
    | nil =>
      have hh := hattach μ q.pivot T P q.gap hq h M G r S
      simpa only [List.flatMap_cons,List.flatMap_nil,List.append_nil,CutPhase.word,
        ordinaryPhaseProduct,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one] using hh
    | cons p ps =>
      obtain ⟨Q⟩ := ih (by simp) htail h M G r hr S
      have hh := hattach μ q.pivot T P q.gap hq _ _ _ _ Q
      simpa only [List.flatMap_cons,CutPhase.word,List.append_assoc,ordinaryPhaseProduct,
        List.map_cons,List.prod_cons,mul_pow,mul_assoc,mul_comm,mul_left_comm] using hh

theorem eventually_refined_phase_extension : ∀ᶠ A : ℝ in atTop,
    ∀ μ T P : ℝ, ∀ q : CutPhase, ∀ qs : List CutPhase, qs ≠ [] →
    qs.flatMap CutPhase.word = q.word →
    (∀ p ∈ qs, OrdinaryPhaseParameters A μ p.pivot T P p.gap) →
    PhaseTraceExtension A μ q ((ordinaryPhaseProduct A μ P qs)^2) := by
  filter_upwards [eventually_ordinary_run_extension] with A hrun
  intro μ T P q qs hnonempty hword hgood
  simpa only [WordTraceExtension,PhaseTraceExtension,hword] using hrun μ T P qs hnonempty hgood

end
end StrongSilver
