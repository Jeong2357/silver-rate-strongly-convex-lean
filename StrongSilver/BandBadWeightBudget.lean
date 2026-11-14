-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ProtectedBadWeight
import StrongSilver.BandLongGainBudget

namespace StrongSilver
open ScheduleTree Filter Real
noncomputable section
set_option maxHeartbeats 4200000

local instance (φ : ℝ → ℝ) (P κ δ : ℝ) (t : ScheduleTree) : Decidable (PaddedGood φ P κ δ t) := Classical.propDecidable _

def bandProtectedNodes (κ B μ u : ℝ) (h : List ℝ) : List ParentedScheduleNode :=
  protectedWindowNodes (cappedStep μ B) (bandPad u) κ (outerBandLow u) (outerBandHigh u) (bandEligible μ B u) (cartesian h)

/-- The bad-vertex weight estimate of (4.13), on the protected band,
with every excess, visibility and short-edge budget discharged from the
original stable signed schedule. The tolerance remains arbitrary. -/
theorem eventually_band_bad_weight_budget : ∃ C > 0, ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ critical δ : ℝ, ∀ h : List ℝ,
    1 < κ → 1 < B → B ≤ cap → cap ≤ κ → u ≤ firstAverageLogScale B →
    1/κ ≤ μ → μ ≤ 2/κ → μ*B ≤ 1/2 → 0 ≤ δ → δ ≤ 1/4 →
    (∀ b ∈ h, 1-μ*b ≠ 0) → inverseChargeAbove (κ/4) h μ ≤ critical →
    critical ≤ 34*weightedCount h cap*cap^(-nu) → D κ h ≤ 1 →
    1 ≤ countAbove h B → κ^nu ≤ weightedCount h cap →
    δ^2*((bandProtectedNodes κ B μ u h).map fun q =>
      if PaddedGood (cappedStep μ B) (bandPad u) q.node.reserve δ q.node.source then 0 else
        Real.exp (nu*parentedHeight (cappedStep μ B) (bandPad u) q)).sum ≤ C*weightedCount h cap := by
  obtain ⟨K,hK,hprotected⟩ := protected_bad_weight_charge
  obtain ⟨c,hc,hshort⟩ := band_short_window_weight_charge
  let C := K*bandExcessConstant+23*bandVisibilityConstant+3*bandExcessConstant/c
  have hC : 0 < C := by
    have hE := bandExcessConstant_positive
    have hV := bandVisibilityConstant_positive
    dsimp only [C]
    positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_band_integral_estimates,eventually_band_long_gain_budget] with u hInt hLong
  intro κ B cap μ critical δ h hκ hB hBcap hcapκ hU hμ hμu hμB hδ hδmax hcrit hcritical hcriticalRank hD hcount hκW
  have hκ0 := zero_lt_one.trans hκ
  have hB0 := zero_lt_one.trans hB
  have hμ0 := (one_div_pos.mpr hκ0).trans_le hμ
  have HInt := hInt κ B cap μ critical h hκ hB hBcap hcapκ hU hμ hμu hμB hcrit hcritical hcriticalRank hD hcount hκW
  have HLong := hLong κ B cap μ critical h hκ hB hBcap hcapκ hU hμ hμu hμB hcrit hcritical hcriticalRank hD hcount hκW
  have HShort := hshort κ B cap μ u h hκ0.le hB0.le HInt
  have HProtected := hprotected (cappedStep μ B) (bandPad u) κ (outerBandLow u) (outerBandHigh u) δ
    (bandEligible μ B u) (cartesian h) (cappedStep_monotone hμ0 (by linarith only [hμB]))
    (Real.exp_pos _) hκ0.le (by simp only [cappedStep,if_pos hB0.le,logarithmicStep_zero,le_refl]) hδ hδmax (cartesian_valid h)
  rw [band_windowNodeExcess_sum hκ0.le hB0.le] at HProtected
  have HE := mul_le_mul_of_nonneg_left HInt.excess_upper hK.le
  have HS : ((parentedNodes 0 κ none (cartesian h)).map
      (shortWindowWeight (cappedStep μ B) (bandPad u) (outerBandLow u) (outerBandHigh u))).sum ≤
      (3*bandExcessConstant/c)*weightedCount h cap := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hc).mpr
    linear_combination HShort
  dsimp only [C,bandProtectedNodes,bandLongVisibleNodes] at *
  linear_combination HProtected+HE+23*HLong+HS

end
end StrongSilver
