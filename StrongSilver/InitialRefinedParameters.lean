-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PhaseRefinement
import StrongSilver.InitialTrackedParameters

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 1800000

/-- Every descendant of a good original initial phase has the closed
ordinary parameters at the refined cutoff. Its entire actual gap is a
subsequence of the original gap, so neither signed mass nor negative-step
charge requires an additional assumption. -/
theorem eventually_initial_refined_parameters : ∀ᶠ A : ℝ in atTop,
    ∀ κ B μ T P : ℝ, ∀ q : CutPhase, ∀ choose : ℕ → ℝ → Bool,
      A ≤ B → κ ≤ A^((1003 : ℝ)/1000) →
      A^((49 : ℝ)/50) ≤ P → P ≤ A^((199 : ℝ)/200) →
      InitialPhaseBudget B μ q.pivot T κ B q.gap →
      (∀ i b, choose i b = true → A ≤ b) → (∀ i b, choose i b = false → 0 < b → b ≤ A) →
      ∀ z ∈ refinePhase choose q, OrdinaryPhaseParameters A μ z.pivot T P z.gap := by
  filter_upwards [eventually_gt_atTop (0 : ℝ),eventually_initial_tracked_parameters] with A hA hparams
  intro κ B μ T P q choose hAB hκA hPL hPU W hselected hunselected z hz
  have hgapSub := refinePhase_gap_sublist hz
  have hbA := refinePhase_pivot_lower hselected (hAB.trans W.pivot_lower) hz
  have hborig : z.pivot ≤ q.pivot := by
    rcases refinePhase_pivot_mem hz with hmem | he
    · by_cases hb0 : 0 < z.pivot
      · exact (W.gap_cap z.pivot hmem hb0).trans W.pivot_lower
      · exact (le_of_not_gt hb0).trans W.pivot_positive.le
    · exact he.le
  have Wz : InitialPhaseBudget A μ z.pivot T κ A z.gap := {
    mu_positive := W.mu_positive
    kappa_large := W.kappa_large
    cutoff_lower := le_rfl
    B_positive := hA
    B_le_kappa := hAB.trans W.B_le_kappa
    pivot_lower := hbA
    pivot_upper := hborig.trans W.pivot_upper
    pivot_lt_time := hborig.trans_lt W.pivot_lt_time
    time_lower := W.time_lower
    time_upper := W.time_upper
    cap_ratio := (div_le_div_of_nonneg_right hAB W.time_positive.le).trans W.cap_ratio
    curvature := W.curvature
    mass := (positiveMass_sublist_le hgapSub).trans W.mass
    gap_cap := refinePhase_gap_cap hunselected hz
    negative_charge := (negativeLogSum_sublist_le W.time_positive hgapSub).trans W.negative_charge
  }
  exact hparams μ z.pivot T κ A P z.gap Wz hκA hPL hPU

end
end StrongSilver
