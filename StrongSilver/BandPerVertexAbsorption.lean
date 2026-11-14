-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandForestDepth

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 3400000

/-- The per-pivot price times the O(2^d) component size is eventually
smaller than every fixed normalized bad-vertex excess c delta^2. -/
theorem eventually_band_per_vertex_absorption {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c) :
    ∀ᶠ u : ℝ in atTop, C*(2:ℝ)^fourPhaseDepth u/u ≤ c*(bandTolerance u)^2 := by
  filter_upwards [eventually_const_mul_log_pow_mul_power_le 3 (2*C) (by norm_num : -(4:ℝ)/5 < 0) hc,
    Real.tendsto_log_atTop.eventually_ge_atTop (1:ℝ),eventually_gt_atTop (0:ℝ)] with u H hlog hu
  have hδ : 0 < bandTolerance u := Real.rpow_pos_of_pos hu _
  have hδeq : (bandTolerance u)^2 = u^(-(1:ℝ)/5) := by
    unfold bandTolerance
    rw [pow_two,← Real.rpow_add hu]
    norm_num
  have he : u^(-(4:ℝ)/5)*(bandTolerance u)^2 = 1/u := by
    rw [hδeq,← Real.rpow_add hu]
    norm_num [Real.rpow_neg_one,one_div]
  have hm := mul_le_mul_of_nonneg_right H (sq_nonneg (bandTolerance u))
  rw [mul_assoc,he] at hm
  have hgroup := (fourPhaseDepth_group_count_bounds hlog).2
  have hg := mul_le_mul_of_nonneg_left hgroup hC
  have hh := div_le_div_of_nonneg_right hg hu.le
  have hid : C*(2*(Real.log u)^3)/u = (2*C*(Real.log u)^3)*(1/u) := by ring
  exact hh.trans (by simpa only [hid] using hm)

/-- Finite arithmetic absorption for a binary component. -/
theorem finite_forest_price_absorption {count bad M price charge excess : ℝ}
    (hbad : 0 ≤ bad) (hprice : 0 ≤ price)
    (hcount : count ≤ M*(bad+1)) (hcharge : charge*bad ≤ excess) (hsmall : price*M ≤ charge) :
    price*count-excess ≤ price*M := by
  have h1 := mul_le_mul_of_nonneg_left hcount hprice
  have h2 := mul_le_mul_of_nonneg_right hsmall hbad
  linear_combination h1+h2+hcharge

end
end StrongSilver
