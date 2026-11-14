-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PolylogMargins

namespace StrongSilver
open Real Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 2400000

theorem eventually_const_mul_log_rpow_le_power (s C : ℝ) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ A : ℝ in atTop, C*(Real.log A)^s ≤ A^r := by
  have ht := ((isLittleO_log_rpow_rpow_atTop s hr).tendsto_div_nhds_zero.const_mul C)
  simp only [mul_zero] at ht
  filter_upwards [eventually_gt_atTop (0:ℝ),(tendsto_order.1 ht).2 1 zero_lt_one] with A hA hh
  have hp := mul_le_mul_of_nonneg_right hh.le (Real.rpow_pos_of_pos hA r).le
  have he : C*((Real.log A)^s/A^r)*A^r = C*(Real.log A)^s := by
    field_simp [(Real.rpow_pos_of_pos hA r).ne']
  rw [he,one_mul] at hp
  exact hp

theorem tendsto_const_mul_log_rpow_mul_power (s C : ℝ) {r : ℝ} (hr : r < 0) :
    Tendsto (fun A : ℝ => C*(Real.log A)^s*A^r) atTop (𝓝 0) := by
  have ht := (isLittleO_log_rpow_rpow_atTop s (neg_pos.mpr hr)).tendsto_div_nhds_zero.const_mul C
  simp only [mul_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with A hA
  rw [Real.rpow_neg hA.le,div_inv_eq_mul]
  ring

theorem eventually_const_mul_log_rpow_mul_power_le (s C : ℝ) {r ε : ℝ} (hr : r < 0) (hε : 0 < ε) :
    ∀ᶠ A : ℝ in atTop, C*(Real.log A)^s*A^r ≤ ε :=
  ((tendsto_order.1 (tendsto_const_mul_log_rpow_mul_power s C hr)).2 ε hε).mono (fun _ h => h.le)

theorem eventually_const_mul_log_rpow_mul_power_le_inverse_log (s C : ℝ) {r : ℝ} (hr : r < 0) :
    ∀ᶠ A : ℝ in atTop, C*(Real.log A)^s*A^r ≤ 1/Real.log A := by
  filter_upwards [eventually_gt_atTop (1:ℝ),eventually_const_mul_log_rpow_mul_power_le (s+1) C hr zero_lt_one]
    with A hA hh
  have hlog := Real.log_pos hA
  have he : (Real.log A)^(s+1) = (Real.log A)^s*Real.log A := by
    rw [Real.rpow_add hlog,Real.rpow_one]
  rw [he] at hh
  apply (le_div_iff₀ hlog).mpr
  nlinarith only [hh]

end
end StrongSilver
