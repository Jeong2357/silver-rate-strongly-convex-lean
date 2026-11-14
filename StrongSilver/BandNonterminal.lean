-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.TerminalNodeReserve
import StrongSilver.BandEligibleUpper
import StrongSilver.CutPowerCrudeUpper

namespace StrongSilver
open ScheduleTree Filter Real
noncomputable section
set_option maxHeartbeats 3400000

/-- A balanced actual band vertex is nonterminal when the global
starting cap is at most kappa/128, as in the chosen counterexample sequence. -/
theorem eventually_band_balanced_nonterminal : ∀ᶠ u : ℝ in atTop,
    ∀ κ B μ δ : ℝ, ∀ h : List ℝ, ∀ q : ParentedScheduleNode,
    0 < κ → 1 < B → B ≤ κ/128 → u ≤ firstAverageLogScale B → 0 < μ → μ*B ≤ 1/2 →
    0 ≤ δ → δ ≤ 1/4 → q ∈ parentedNodes 0 κ none (cartesian h) →
    bandEligible μ B u q.node.pivotIndex q.node.pivot = true →
    PaddedBalanced (cappedStep μ B) (bandPad u) q.node.reserve δ q.node.source → q.node.reserve = 0 := by
  filter_upwards [eventually_eligible_band_step,eventually_eligible_band_step_upper] with u hstep hupper
  intro κ B μ δ h q hκ hB hBκ hU hμ hμB hδ hδmax hq helig hb
  rcases parentedNodes_reserve_zero_or_original hq with hz | hz
  · exact hz
  · have hroot := hb.root_positive
    have hbB := hupper B μ q.node.pivot q.node.pivotIndex hB hU hμ hμB helig
    have hUpper := cappedStep_positive_upper hμ (zero_lt_one.trans hB) hμB hbB
    have hb0 := (hstep B μ q.node.pivot q.node.pivotIndex hB hU hμ hμB helig).1
    rw [max_eq_left hb0.le] at hUpper
    have hφ : cappedStep μ B q.node.pivot ≤ 2*q.node.pivot :=
      (le_max_left _ _).trans hUpper
    have hsmall : 5*(cappedStep μ B q.node.source.rootStep-bandPad u) < κ := by
      have hP := Real.exp_pos ((987:ℝ)/1000*u)
      change 0 < bandPad u at hP
      have hh := mul_le_mul_of_nonneg_left hbB (by norm_num : (0:ℝ) ≤ 10)
      change cappedStep μ B q.node.source.rootStep ≤ 2*q.node.pivot at hφ
      nlinarith only [hφ,hP,hh,hBκ,hκ]
    have hzero : cappedStep μ B 0 ≤ 0 := by simp only [cappedStep,if_pos (zero_lt_one.trans hB).le,logarithmicStep_zero,le_refl]
    rw [hz] at hb
    exact False.elim (padded_terminal_unbalanced (Real.exp_pos _) hκ.le hzero hroot hδ hδmax hsmall hb)

end
end StrongSilver
