-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.Counterexamples

namespace StrongSilver
open Filter
open scoped Topology
noncomputable section

def CounterexampleSequence.threshold {a : ℝ} (S : CounterexampleSequence a) (j : ℕ) : ℝ :=
  (exists_weightedCount_maximizer (S.schedules j) (a*S.kappa j) (S.weight_positive j)).choose

theorem CounterexampleSequence.threshold_positive {a : ℝ} (S : CounterexampleSequence a) (j : ℕ) :
    0 < S.threshold j :=
  (exists_weightedCount_maximizer (S.schedules j) (a*S.kappa j) (S.weight_positive j)).choose_spec.1

theorem CounterexampleSequence.threshold_le_cap {a : ℝ} (S : CounterexampleSequence a) (j : ℕ) :
    S.threshold j ≤ a*S.kappa j :=
  (exists_weightedCount_maximizer (S.schedules j) (a*S.kappa j) (S.weight_positive j)).choose_spec.2.1

theorem CounterexampleSequence.threshold_maximizes {a : ℝ} (S : CounterexampleSequence a) (j : ℕ) :
    (S.threshold j)^nu*(countAbove (S.schedules j) (S.threshold j) : ℝ) =
      weightedCount (S.schedules j) (a*S.kappa j) :=
  (exists_weightedCount_maximizer (S.schedules j) (a*S.kappa j) (S.weight_positive j)).choose_spec.2.2

theorem CounterexampleSequence.ratio_le_threshold_power {a : ℝ} (S : CounterexampleSequence a) (j : ℕ) :
    weightedCount (S.schedules j) (a*S.kappa j)/((S.schedules j).length : ℝ) ≤ (S.threshold j)^nu := by
  have hn : (0 : ℝ) < (S.schedules j).length := by exact_mod_cast S.length_pos j
  apply (div_le_iff₀ hn).mpr
  rw [← S.threshold_maximizes j]
  apply mul_le_mul_of_nonneg_left
  · exact_mod_cast countAbove_le_length (S.schedules j) (S.threshold j)
  · exact Real.rpow_nonneg (S.threshold_positive j).le nu

theorem CounterexampleSequence.threshold_escape {a : ℝ} (S : CounterexampleSequence a) :
    Tendsto S.threshold atTop atTop := by
  apply tendsto_atTop.mpr
  intro A
  let M := max A 1
  filter_upwards [S.ratio_escape.eventually_ge_atTop (M^nu+1)] with j hj
  by_contra hn
  have hm : S.threshold j ≤ M := (le_of_not_ge hn).trans (le_max_left _ _)
  have hp := Real.rpow_le_rpow (S.threshold_positive j).le hm nu_positive.le
  have hratio := S.ratio_le_threshold_power j
  linarith

end
end StrongSilver
