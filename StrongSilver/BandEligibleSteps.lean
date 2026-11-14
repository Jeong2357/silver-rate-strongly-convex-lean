-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandLogWindow

namespace StrongSilver
open Real Filter Set
noncomputable section
set_option maxHeartbeats 3000000

def bandPad (u : ℝ) : ℝ := Real.exp ((987:ℝ)/1000*u)
def bandCutoff (μ u y : ℝ) : ℝ := logarithmicCutoff μ (bandPad u) y

def bandEligible (μ B u : ℝ) (_ : ℕ) (b : ℝ) : Bool :=
  decide (bandPad u < cappedStep μ B b ∧
    Real.log (cappedStep μ B b-bandPad u) ∈ Icc (outerBandLow u) (outerBandHigh u))

/-- Eligible transformed heights correspond to actual steps in the
same uniform logarithmic window, including above-cap step candidates. -/
theorem eventually_eligible_band_step : ∀ᶠ u : ℝ in atTop,
    ∀ B μ b : ℝ, ∀ j : ℕ, 1 < B → u ≤ firstAverageLogScale B → 0 < μ → μ*B ≤ 1/2 →
    bandEligible μ B u j b = true →
    0 < b ∧ (999:ℝ)/1000*u ≤ Real.log b ∧ Real.log b ≤ (1001:ℝ)/1000*u ∧ 2*bandPad u ≤ b := by
  filter_upwards [eventually_outer_band_log_window] with u hwindow
  intro B μ b j hB hU hμ hμB heligible
  have he := of_decide_eq_true heligible
  change bandPad u < cappedStep μ B b ∧
    Real.log (cappedStep μ B b-bandPad u) ∈ Icc (outerBandLow u) (outerBandHigh u) at he
  let y := Real.log (cappedStep μ B b-bandPad u)
  have W := hwindow B μ y hB hU hμ hμB he.2
  have hbranch := W.2.2.2.2.2.2.2.2.2.2
  change cappedStep μ B (bandCutoff μ u y) = bandPad u+Real.exp y at hbranch
  have hright : bandPad u+Real.exp y = cappedStep μ B b := by
    dsimp only [y]
    rw [Real.exp_log (sub_pos.mpr he.1)]
    ring
  rw [hright] at hbranch
  have hcut : bandCutoff μ u y = b := (cappedStep_strictMono hμ (by linarith only [hμB])).injective hbranch
  have hpos : 0 < bandCutoff μ u y := W.2.2.1
  have hlo : (999:ℝ)/1000*u ≤ Real.log (bandCutoff μ u y) := W.2.2.2.1
  have hhi : Real.log (bandCutoff μ u y) ≤ (1001:ℝ)/1000*u := W.2.2.2.2.1
  have hpad : 2*bandPad u ≤ bandCutoff μ u y := W.2.2.2.2.2.2.2.1
  simpa only [hcut] using And.intro hpos (And.intro hlo (And.intro hhi hpad))

/-- Every working-cut threshold in the window escapes uniformly,
independently of the schedule and the chosen curvature. -/
theorem eventually_band_cutoff_ge (M : ℝ) : ∀ᶠ u : ℝ in atTop,
    ∀ B μ y : ℝ, 1 < B → u ≤ firstAverageLogScale B → 0 < μ → μ*B ≤ 1/2 →
    y ∈ Icc (outerBandLow u) (outerBandHigh u) → M ≤ bandCutoff μ u y := by
  filter_upwards [eventually_outer_band_log_window,
    eventually_ge_atTop (Real.log (max M 1)/((999:ℝ)/1000))] with u hwindow hu
  intro B μ y hB hU hμ hμB hy
  have W := hwindow B μ y hB hU hμ hμB hy
  have hcut : 0 < bandCutoff μ u y := W.2.2.1
  have hlog : (999:ℝ)/1000*u ≤ Real.log (bandCutoff μ u y) := W.2.2.2.1
  have hbase : Real.log (max M 1) ≤ (999:ℝ)/1000*u := by
    have hh := (div_le_iff₀ (by norm_num : (0:ℝ) < 999/1000)).mp hu
    nlinarith only [hh]
  have he := Real.exp_le_exp.mpr (hbase.trans hlog)
  rw [Real.exp_log (lt_of_lt_of_le zero_lt_one (le_max_right M 1)),Real.exp_log hcut] at he
  exact (le_max_left M 1).trans he

end
end StrongSilver
