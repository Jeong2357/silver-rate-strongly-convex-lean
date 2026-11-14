-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.NearBadChildCharge
import StrongSilver.BandBadWeightRate

namespace StrongSilver
open ScheduleTree Real Filter
noncomputable section
set_option maxHeartbeats 3800000

/-- The nearby bad-child contribution in (4.23) is at most O(W u^(3/5)),
using the actual good-node tolerance and the original bad-vertex budget. -/
theorem eventually_band_near_bad_child_rate : ∃ C > 0, ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ critical : ℝ, ∀ h : List ℝ,
    1 < κ → 1 < B → B ≤ cap → cap ≤ κ → u ≤ firstAverageLogScale B →
    1/κ ≤ μ → μ ≤ 2/κ → μ*B ≤ 1/2 →
    (∀ b ∈ h, 1-μ*b ≠ 0) → inverseChargeAbove (κ/4) h μ ≤ critical →
    critical ≤ 34*weightedCount h cap*cap^(-nu) → D κ h ≤ 1 →
    1 ≤ countAbove h B → κ^nu ≤ weightedCount h cap →
    (((parentedNodes 0 κ none (cartesian h)).filter fun q =>
      @decide (NearBadChildAt (cappedStep μ B) (bandPad u) κ (outerBandLow u) (outerBandHigh u)
        (bandTolerance u) (Real.log u/2) (bandEligible μ B u) (cartesian h) q) (Classical.propDecidable _)).map
        (parentWeight (cappedStep μ B) (bandPad u))).sum ≤ C*weightedCount h cap*u^((3:ℝ)/5) := by
  obtain ⟨C,hC,H⟩ := eventually_band_bad_weight_rate
  refine ⟨C,hC,?_⟩
  filter_upwards [H,eventually_ge_atTop (1:ℝ)] with u hBad hu
  intro κ B cap μ critical h hκ hB hBcap hcapκ hU hμ hμu hμB hcrit hcritical hcriticalRank hD hcount hκW
  have hu0 := zero_lt_one.trans_le hu
  have hBad' := hBad κ B cap μ critical h hκ hB hBcap hcapκ hU hμ hμu hμB hcrit hcritical hcriticalRank hD hcount hκW
  have hNear := near_bad_child_weight_charge (cappedStep μ B) (bandPad u) κ (outerBandLow u) (outerBandHigh u)
    (bandTolerance u) (Real.log u/2) (bandEligible μ B u) (cartesian h)
  have hScale := mul_le_mul_of_nonneg_left hBad' (Real.exp_pos (nu*(Real.log u/2))).le
  have hExp : Real.exp (nu*(Real.log u/2)) = u^(nu/2) := by
    rw [Real.rpow_def_of_pos hu0]
    congr 1
    ring
  rw [hExp] at hNear hScale
  have hPower : u^(nu/2+(1:ℝ)/5) ≤ u^((3:ℝ)/5) :=
    Real.rpow_le_rpow_of_exponent_le hu (by linarith only [nu_lt_four_fifths])
  rw [Real.rpow_add hu0] at hPower
  have hCoeff : 0 ≤ C*weightedCount h cap := mul_nonneg hC.le (weightedCount_nonneg h cap)
  have hFinal := mul_le_mul_of_nonneg_left hPower hCoeff
  dsimp only [bandProtectedNodes] at hScale
  linear_combination hNear+hScale+hFinal

end
end StrongSilver
