-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandEligibleSteps

namespace StrongSilver
open Real Filter Set
noncomputable section
set_option maxHeartbeats 3000000

/-- Eligible band pivots lie below the actual weighted-maximizing
threshold. The cap transform cannot introduce an above-threshold pivot. -/
theorem eventually_eligible_band_step_upper : ∀ᶠ u : ℝ in atTop,
    ∀ B μ b : ℝ, ∀ j : ℕ, 1 < B → u ≤ firstAverageLogScale B → 0 < μ → μ*B ≤ 1/2 →
    bandEligible μ B u j b = true → b ≤ B := by
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
  have hupper : bandCutoff μ u y ≤ B^(1-firstAverageEta) := W.2.2.2.2.2.2.2.2.1
  have hBB : B^(1-firstAverageEta) ≤ B := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hB.le
      (show 1-firstAverageEta ≤ (1:ℝ) by linarith only [firstAverageEta_bounds.1])
  simpa only [hcut] using hupper.trans hBB

end
end StrongSilver
