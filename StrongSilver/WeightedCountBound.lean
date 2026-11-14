-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CounterexampleBandPower
import StrongSilver.TargetReduction

namespace StrongSilver
open Real Filter
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 9500000

/-- Section 5: the lower and upper bounds for the same total averaged
power decrease contradict every unbounded weighted-count sequence. -/
theorem no_counterexample_sequence {a : ℝ} (ha : 0 < a) (hamax : a ≤ 1/1000000)
    (htrack : 7*initialMarkedLogCoefficient a ≤ 1/2)
    (herror : 2*splitCoefficient*initialStableErrorCoefficient a ≤ powerLogMinimum/16) :
    ¬Nonempty (CounterexampleSequence a) := by
  rintro ⟨S⟩
  obtain ⟨K,hK,Hupper⟩ := S.eventually_total_band_power_upper ha hamax
  have hLower := S.eventually_averaged_power_drop ha (hamax.trans (by norm_num)) htrack herror
  have hY := finalAverageLogScale_escape.comp S.ratio_escape
  have hTail := geometric_band_rate_tail_tendsto_zero bandRatio_bounds.1 (by norm_num : (0:ℝ) < 1/1000)
  have hZero := (hTail.comp hY).const_mul K
  simp only [mul_zero] at hZero
  have hSmall := hZero.eventually_lt_const
    (show (0:ℝ) < powerLogMinimum/32 by exact div_pos powerLogMinimum_positive (by norm_num))
  have hImpossible : ∀ᶠ j : ℕ in atTop, False := by
    filter_upwards [hLower,Hupper,hSmall] with j hl hu hs
    dsimp only [Function.comp_def] at hl hu hs
    norm_num only at hl hu hs
    obtain ⟨μ,m,hμ,hμu,hcrit,hquarter,hm,hYm,hmY,hScales,hDrop⟩ := hl
    have hTotal := hu μ hμ hμu hcrit hquarter m hScales
    have hW := S.weight_positive j
    have hStrict := mul_lt_mul_of_pos_right hs hW
    have hWeak := hDrop.trans hTotal
    nlinarith only [hStrict,hWeak]
  obtain ⟨j,hj⟩ := hImpossible.exists
  exact hj

/-- The weighted count is bounded by an absolute multiple of schedule
length. There are no unproved geometric or analytic hypotheses. -/
theorem weighted_count_bound {a : ℝ} (ha : 0 < a) (hamax : a ≤ 1/1000000)
    (htrack : 7*initialMarkedLogCoefficient a ≤ 1/2)
    (herror : 2*splitCoefficient*initialStableErrorCoefficient a ≤ powerLogMinimum/16) :
    WeightedCountBound a := by
  by_contra hn
  exact no_counterexample_sequence ha hamax htrack herror (counterexample_of_not_weightedCountBound ha hn)

/-- An absolute cap satisfying all the finite construction conditions
exists and has the proved weighted-count bound. -/
theorem exists_weighted_count_bound : ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧ WeightedCountBound a := by
  obtain ⟨a,ha,hamax,h128,htrack,herror⟩ := exists_small_initial_cap_below (by norm_num : (0:ℝ) < 1/1000000)
  exact ⟨a,ha,hamax.trans (by norm_num),weighted_count_bound ha hamax htrack herror⟩

end
end StrongSilver
