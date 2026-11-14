-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.DisjointReplacementPlan
import StrongSilver.CompleteCutReplacement

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 3600000

namespace DisjointReplacementPlan

/-- The empty matching retains all ordinary factors. -/
theorem eventually_empty_matching : ∀ᶠ A : ℝ in atTop,
    ∀ μ T P : ℝ, ∀ s : WorkingAssembly, s.Valid A μ T P →
    DisjointReplacementPlan A μ P s 0 := by
  filter_upwards [eventually_ordinary_phase_extension] with A hext
  intro μ T P s hs
  induction s with
  | ordinaryEnd q t =>
    apply ordinaryEnd
    simpa only [WordTraceExtension,PhaseTraceExtension,Real.exp_zero,mul_one] using hext μ T P q hs.1
  | ordinary q s ih =>
    have hh := ordinary q s 0 0 (ih hs.2) (by
      simpa only [WordTraceExtension,PhaseTraceExtension,Real.exp_zero,mul_one] using hext μ T P q hs.1)
    simpa only [add_zero] using hh
  | block q I c s ih => exact block q I c s 0 (ih hs.2.2.2.2.2)
  | blockEnd q I c t => exact blockEnd q I c t
  | noConnector q I t => exact noConnector q I t

end DisjointReplacementPlan

namespace CompleteCutAssembly

/-- An actual disjoint matching on the retained ordinary suffix. -/
def MatchingWitness (A μ P : ℝ) (t : List ℝ) (gain : ℝ) : CompleteCutAssembly → Prop
  | .scalar _ => gain ≤ 0
  | .positive s => DisjointReplacementPlan A μ P (s.erase t) gain
  | .leadingBlock _ _ s => DisjointReplacementPlan A μ P (s.erase t) gain
  | .leadingEnd _ _ => gain ≤ 0

/-- The combinatorial matching produces the actual finite-trajectory
witness required by the full-cut replacement inequality. -/
theorem eventually_matching_witness : ∀ᶠ A : ℝ in atTop,
    ∀ μ T P : ℝ, ∀ s : CompleteCutAssembly, ∀ t : List ℝ, ∀ gain : ℝ,
    s.PhaseValid A μ T P t → s.MatchingWitness A μ P t gain →
    s.ReplacementWitness A μ P t gain := by
  filter_upwards [DisjointReplacementPlan.eventually_realize] with A hrealize
  intro μ T P s t gain hs hm
  cases s with
  | scalar I => exact hm
  | leadingEnd I c => exact hm
  | positive s =>
    have hh := hrealize μ T P (s.erase t) hs gain hm
    simpa only [ReplacementWitness,CutAssembly.erase_word] using hh
  | leadingBlock I c s =>
    have hh := hrealize μ T P (s.erase t) hs gain hm
    simpa only [ReplacementWitness,CutAssembly.erase_word] using hh

end CompleteCutAssembly
end
end StrongSilver
