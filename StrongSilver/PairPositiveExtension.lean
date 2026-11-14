-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CompletePairTests

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 4200000

/-- Every pair of ordinary phases admits the zero-improvement option. -/
theorem eventually_ordinary_pair_extension : ∀ᶠ A : ℝ in atTop,
    ∀ μ T P : ℝ, ∀ a b : CutPhase,
    OrdinaryPhaseParameters A μ a.pivot T P a.gap →
    OrdinaryPhaseParameters A μ b.pivot T P b.gap → PairTraceExtension A μ P (a,b) 0 := by
  filter_upwards [eventually_ordinary_run_extension] with A H
  intro μ T P a b Wa Wb
  have hh := H μ T P [a,b] (by simp) (by intro q hq; simp only [List.mem_cons,List.mem_nil_iff,or_false] at hq; rcases hq with rfl | rfl <;> assumption)
  simpa only [PairTraceExtension,Real.exp_zero,mul_one,List.flatMap_cons,List.flatMap_nil,
    List.append_nil,ordinaryPhaseProduct,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,mul_pow] using hh

/-- A valid positive improvement can be retained while the ordinary
construction supplies zero whenever the candidate score is negative. -/
theorem pairTraceExtension_positive_part {A μ P g : ℝ} {p : CutPhase × CutPhase}
    (h0 : PairTraceExtension A μ P p 0) (hg : PairTraceExtension A μ P p g) :
    PairTraceExtension A μ P p (max g 0) := by
  by_cases h : 0 ≤ g
  · simpa only [max_eq_left h] using hg
  · simpa only [max_eq_right (le_of_not_ge h)] using h0

end
end StrongSilver
