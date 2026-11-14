-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FarChildMassCharge
import StrongSilver.BandFrontierMassBudget

namespace StrongSilver
open ScheduleTree Scalar.SignedIntervals Real Filter Set
noncomputable section
set_option maxHeartbeats 3800000

/-- The far-child charge in one actual height bin has the decay used
in (4.23). All gap-mass budgets are supplied by the original-word rank
bound on the same transformed cutoff. -/
theorem eventually_band_far_child_mass : ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ δ j width : ℝ, ∀ h : List ℝ,
    1 < B → B ≤ cap → u ≤ firstAverageLogScale B → 0 < μ → μ*B ≤ 1/2 →
    0 ≤ δ → δ ≤ 1/4 → 1 < width → j+1-width ∈ Icc (outerBandLow u) (outerBandHigh u) →
    (((parentedNodes 0 κ none (cartesian h)).filter fun q =>
      @decide (FarChildAt (cappedStep μ B) (bandPad u) δ j width q) (Classical.propDecidable _)).map
        (parentWeight (cappedStep μ B) (bandPad u))).sum ≤
      (8/(1-nu))*weightedCount h cap*Real.exp ((nu-1)*(width-1)) := by
  filter_upwards [eventually_band_frontier_mass_budget] with u H
  intro κ B cap μ δ j width h hB hBcap hU hμ hμB hδ hδmax hwidth hy
  have hzero : cappedStep μ B 0 ≤ 0 := by simp only [cappedStep,if_pos (zero_lt_one.trans hB).le,logarithmicStep_zero,le_refl]
  have hCharge := far_child_mass_charge (cappedStep μ B) (cappedStep_monotone hμ (by linarith only [hμB]))
    (P := bandPad u) (κ := κ) (j := j) (width := width) (Real.exp_pos _) hzero hδ hδmax hwidth (cartesian h) (cartesian_valid h)
  have hMass := H κ B cap μ (j+1-width) h hB hBcap hU hμ hμB hy
  have hScale := mul_le_mul_of_nonneg_left hMass
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (Real.exp_pos ((nu-1)*(width-1))).le)
  have hExp : Real.exp ((nu-1)*(width-1))*Real.exp ((nu-1)*(j+1-width)) = Real.exp ((nu-1)*j) := by
    rw [← Real.exp_add]
    congr 1
    ring
  dsimp only [bandIndexedFrontier] at hScale
  have hRearrange (S : ℝ) :
      (2*Real.exp ((nu-1)*(width-1)))*(Real.exp ((nu-1)*(j+1-width))*S) = 2*Real.exp ((nu-1)*j)*S := by
    calc
      _ = 2*(Real.exp ((nu-1)*(width-1))*Real.exp ((nu-1)*(j+1-width)))*S := by ring
      _ = _ := by rw [hExp]
  rw [hRearrange] at hScale
  linear_combination hCharge+hScale

end
end StrongSilver
