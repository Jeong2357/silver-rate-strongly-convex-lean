-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PowerMargins

namespace StrongSilver
open Real Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 2400000

/-- Every fixed power of log u is dominated by every positive power of
u. Constants are chosen before the actual schedule and depth. -/
theorem eventually_const_mul_log_pow_le_power (n : ℕ) (C : ℝ) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ u : ℝ in atTop, C*(Real.log u)^n ≤ u^r := by
  have ht : Tendsto (fun u : ℝ => C*((Real.log u)^n/u^r)) atTop (𝓝 0) := by
    have hh := (isLittleO_log_rpow_rpow_atTop (n:ℝ) hr).tendsto_div_nhds_zero.const_mul C
    simpa only [Real.rpow_natCast,mul_zero] using hh
  filter_upwards [eventually_gt_atTop (0:ℝ),(tendsto_order.1 ht).2 1 zero_lt_one] with u hu hh
  have hp := mul_le_mul_of_nonneg_right hh.le (Real.rpow_pos_of_pos hu r).le
  have he : C*((Real.log u)^n/u^r)*u^r = C*(Real.log u)^n := by
    field_simp
  rw [he,one_mul] at hp
  exact hp

/-- Uniform polylogarithmic losses multiplied by a strictly negative
power tend to zero, in a direct form usable by finite group budgets. -/
theorem eventually_const_mul_log_pow_mul_power_le (n : ℕ) (C : ℝ) {r ε : ℝ}
    (hr : r < 0) (hε : 0 < ε) : ∀ᶠ u : ℝ in atTop, C*(Real.log u)^n*u^r ≤ ε := by
  filter_upwards [eventually_gt_atTop (0:ℝ),eventually_const_mul_log_pow_le_power n (C/ε) (neg_pos.mpr hr)]
    with u hu hh
  have hp := mul_le_mul_of_nonneg_right hh (Real.rpow_pos_of_pos hu r).le
  have hpow : u^(-r)*u^r = 1 := by rw [← Real.rpow_add hu,neg_add_cancel,Real.rpow_zero]
  rw [hpow] at hp
  have he : (C/ε)*(Real.log u)^n*u^r = (C*(Real.log u)^n*u^r)/ε := by ring
  rw [he] at hp
  exact (div_le_one hε).mp hp

end
end StrongSilver
