-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.Constants
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace StrongSilver
open Real
noncomputable section
set_option maxHeartbeats 2400000

/-- Converting the actual-cutoff rank error to the common height
measure costs only an absolute factor on the logarithmic branch. -/
theorem height_rank_error_normalization {A u y W C : ℝ} (hA : 0 < A) (hu : 0 < u)
    (hW : 0 ≤ W) (hC : 0 ≤ C) (hheight : Real.exp y ≤ 2*A) (hlog : u/2 ≤ Real.log A) :
    Real.exp (nu*y)*(C*W*A^(-nu)/Real.log A) ≤ 4*C*W/u := by
  have hlog0 : 0 < Real.log A := (by linarith only [hu] : 0 < u/2).trans_le hlog
  have heq : Real.exp (nu*y) = (Real.exp y)^nu := by
    rw [Real.rpow_def_of_pos (Real.exp_pos y),Real.log_exp]
    congr 1
    ring
  have hpow := Real.rpow_le_rpow (Real.exp_pos y).le hheight nu_positive.le
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hA.le] at hpow
  have htwo : (2:ℝ)^nu ≤ 2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) nu_lt_one.le
  have hexp : Real.exp (nu*y) ≤ 2*A^nu := by
    rw [heq]
    exact hpow.trans (mul_le_mul_of_nonneg_right htwo (Real.rpow_pos_of_pos hA nu).le)
  have hm := mul_le_mul_of_nonneg_right hexp (show 0 ≤ C*W*A^(-nu)/Real.log A by positivity)
  have hcancel : A^nu*A^(-nu) = 1 := by rw [← Real.rpow_add hA,add_neg_cancel,Real.rpow_zero]
  have hm' : Real.exp (nu*y)*(C*W*A^(-nu)/Real.log A) ≤ 2*C*W/Real.log A := by
    have he : 2*A^nu*(C*W*A^(-nu)/Real.log A) = 2*C*W/Real.log A := by
      calc
        _ = 2*C*W*(A^nu*A^(-nu))/Real.log A := by ring
        _ = _ := by rw [hcancel,mul_one]
    rwa [he] at hm
  have hdiv := div_le_div_of_nonneg_left (show 0 ≤ 2*C*W by positivity)
    (by linarith only [hu] : 0 < u/2) hlog
  have hid : 2*C*W/(u/2) = 4*C*W/u := by ring
  rw [hid] at hdiv
  exact hm'.trans hdiv

end
end StrongSilver
