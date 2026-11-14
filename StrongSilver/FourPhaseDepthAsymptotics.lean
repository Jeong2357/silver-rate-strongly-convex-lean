-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseDepthBounds
import StrongSilver.PolylogMargins

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 2400000

theorem eventually_fourPhaseDepth_le_power {r : ℝ} (hr : 0 < r) :
    ∀ᶠ u : ℝ in atTop, (fourPhaseDepth u:ℝ) ≤ u^r := by
  let C := 3/Real.log 2+1
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)),
    eventually_const_mul_log_pow_le_power 1 C hr] with u hu hsmall
  have hlog2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hlogu : 0 < Real.log u := zero_lt_one.trans_le hu
  have hloglog := (Real.log_le_sub_one_of_pos hlogu).trans (by linarith : Real.log u-1 ≤ Real.log u)
  have hmul := mul_le_mul_of_nonneg_left hloglog (show 0 ≤ 3/Real.log 2 by positivity)
  have hd := (fourPhaseDepth_bounds hu).2.le
  have he : 3*Real.log (Real.log u)/Real.log 2 = (3/Real.log 2)*Real.log (Real.log u) := by ring
  rw [he] at hd
  simp only [pow_one] at hsmall
  have hbound : (fourPhaseDepth u:ℝ) ≤ C*Real.log u := by
    dsimp only [C]
    nlinarith only [hd,hmul,hu]
  exact hbound.trans hsmall

theorem eventually_fourPhaseGroupCount_le_power {r : ℝ} (hr : 0 < r) :
    ∀ᶠ u : ℝ in atTop, (2:ℝ)^fourPhaseDepth u ≤ u^r := by
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)),
    eventually_const_mul_log_pow_le_power 3 2 hr] with u hu hsmall
  exact (fourPhaseDepth_group_count_bounds hu).2.trans hsmall

theorem eventually_fourPhaseScaleDenominator_le_power {r : ℝ} (hr : 0 < r) :
    ∀ᶠ u : ℝ in atTop, (4:ℝ)^(fourPhaseDepth u+2) ≤ u^r := by
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)),
    eventually_const_mul_log_pow_le_power 6 64 hr] with u hu hsmall
  exact (fourPhaseDepth_scale_denominator hu).trans hsmall

theorem fourPhaseDepth_inverse_group_bound {u : ℝ} (hu : 1 ≤ Real.log u) :
    1/(2:ℝ)^fourPhaseDepth u ≤ 1/(Real.log u)^3 := by
  exact div_le_div_of_nonneg_left (by norm_num) (pow_pos (zero_lt_one.trans_le hu) _)
    (fourPhaseDepth_group_count_bounds hu).1

end
end StrongSilver
