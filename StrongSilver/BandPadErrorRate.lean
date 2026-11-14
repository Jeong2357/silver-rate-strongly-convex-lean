-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandPadRatio
import StrongSilver.BandKernelErrorRate

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 4300000

/-- The common offset contributes a fixed negative power after the
original capped rank normalization at the lower threshold. -/
theorem eventually_band_pad_rank_error : ∀ᶠ u : ℝ in atTop,
    (bandPad u)^nu*Real.exp (-nu*(u/bandRatio)) ≤ u^(-(1:ℝ)/1000) := by
  have hν := nu_positive
  have hc : 0 < nu/100 := by positivity
  filter_upwards [eventually_exp_negative_linear_le_inverse hc,eventually_ge_atTop (1:ℝ)] with u hExp hu
  have hu0 := zero_lt_one.trans_le hu
  have hr := zero_lt_one.trans bandRatio_bounds.1
  have hrUpper : bandRatio ≤ (10001:ℝ)/10000 := by
    unfold bandRatio
    linarith only [firstAverageEta_bounds.2]
  have hDiv : (9998:ℝ)/10000*u ≤ u/bandRatio := by
    apply (le_div_iff₀ hr).mpr
    have hh := mul_le_mul_of_nonneg_right hrUpper hu0.le
    nlinarith only [hh,hu0]
  have hArg : ((987:ℝ)/1000*u)*nu-nu*(u/bandRatio) ≤ -(nu/100)*u := by
    have hh := mul_le_mul_of_nonneg_left hDiv hν.le
    nlinarith only [hh,hu0,hν]
  have hEq : (bandPad u)^nu*Real.exp (-nu*(u/bandRatio)) =
      Real.exp (((987:ℝ)/1000*u)*nu-nu*(u/bandRatio)) := by
    unfold bandPad
    rw [Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp,← Real.exp_add]
    congr 1
    ring
  have hInv : 1/u ≤ u^(-(1:ℝ)/1000) := by
    rw [one_div,← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hu (by norm_num)
  rw [hEq]
  exact (Real.exp_le_exp.mpr hArg).trans (hExp.trans hInv)

end
end StrongSilver
