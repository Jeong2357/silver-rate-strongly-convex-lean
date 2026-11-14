-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CounterexampleThresholds

namespace StrongSilver
open Filter
open scoped Topology
noncomputable section

theorem CounterexampleSequence.length_over_weight_tendsto_zero {a : ℝ} (S : CounterexampleSequence a) :
    Tendsto (fun j => ((S.schedules j).length : ℝ)/weightedCount (S.schedules j) (a*S.kappa j)) atTop (𝓝 0) := by
  have hh := tendsto_inv_atTop_zero.comp S.ratio_escape
  simpa only [Function.comp_def,inv_div] using hh

theorem CounterexampleSequence.eventually_terminal_power_small {a c : ℝ} (S : CounterexampleSequence a) (hc : 0 < c) :
    ∀ᶠ j : ℕ in atTop, (S.kappa j)^nu ≤ c*weightedCount (S.schedules j) (a*S.kappa j) := by
  filter_upwards [(tendsto_order.1 S.length_over_weight_tendsto_zero).2 c hc] with j hj
  have hh := (div_le_iff₀ (S.weight_positive j)).mp hj.le
  exact (S.length_large j).trans hh

end
end StrongSilver
