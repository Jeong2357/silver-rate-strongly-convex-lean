-- SPDX-License-Identifier: GPL-3.0-only
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace StrongSilver
open Real Filter
open scoped Topology
noncomputable section

theorem eventually_const_mul_power_le {r s : ℝ} (hrs : r < s) (C : ℝ) :
    ∀ᶠ A : ℝ in atTop, C*A^r ≤ A^s := by
  have ht : Tendsto (fun A : ℝ => C*A^(r-s)) atTop (𝓝 0) := by
    have hpow := tendsto_rpow_neg_atTop (sub_pos.mpr hrs)
    simpa only [neg_sub,mul_zero] using hpow.const_mul C
  filter_upwards [eventually_gt_atTop (0 : ℝ),(tendsto_order.1 ht).2 1 zero_lt_one] with A hA hh
  have hm := mul_le_mul_of_nonneg_right hh.le (Real.rpow_pos_of_pos hA s).le
  have he : C*A^(r-s)*A^s = C*A^r := by
    rw [mul_assoc,← Real.rpow_add hA]
    congr 1
    congr 1
    ring
  rw [he,one_mul] at hm
  exact hm

theorem eventually_const_mul_negative_power_le_inverse_log {r : ℝ} (hr : r < 0) (C : ℝ) :
    ∀ᶠ A : ℝ in atTop, C*A^r ≤ 1/Real.log A := by
  have ht0 : Tendsto (fun A : ℝ => Real.log A/A^(-r)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (neg_pos.mpr hr)).tendsto_div_nhds_zero
  have ht := ht0.const_mul C
  simp only [mul_zero] at ht
  filter_upwards [eventually_gt_atTop (1 : ℝ),(tendsto_order.1 ht).2 1 zero_lt_one] with A hA hh
  have hApos : 0 < A := zero_lt_one.trans hA
  have he : C*(Real.log A/A^(-r)) = C*A^r*Real.log A := by
    rw [Real.rpow_neg hApos.le]
    simp only [div_inv_eq_mul]
    ring
  rw [he] at hh
  exact (le_div_iff₀ (Real.log_pos hA)).mpr hh.le

end
end StrongSilver
