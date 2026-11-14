-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PowerMargins
import StrongSilver.Constants

namespace StrongSilver
open Real Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 2000000

theorem tendsto_negative_rpow_mul_log {r : ℝ} (hr : r < 0) :
    Tendsto (fun B : ℝ => B^r*Real.log B) atTop (𝓝 0) := by
  have hh := (isLittleO_log_rpow_atTop (neg_pos.mpr hr)).tendsto_div_nhds_zero
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with B hB
  rw [Real.rpow_neg hB.le,div_inv_eq_mul]
  ring

theorem far_cutoff_root_bound {B κ ε : ℝ} (hB : 0 < B) (hκ : 0 < κ) (hε : ε < 1)
    (hfar : B ≤ κ^(1-ε)) : B^(1/(1-ε)) ≤ κ := by
  have hd : 0 < 1-ε := sub_pos.mpr hε
  have hh := Real.rpow_le_rpow hB.le hfar (one_div_nonneg.mpr hd.le)
  rw [← Real.rpow_mul hκ.le,show (1-ε)*(1/(1-ε)) = (1 : ℝ) by field_simp,Real.rpow_one] at hh
  exact hh

theorem far_cutoff_ratio_bound {B κ ε : ℝ} (hB : 0 < B) (hκ : 0 < κ) (hε : ε < 1)
    (hfar : B ≤ κ^(1-ε)) : B/κ ≤ B^(-ε/(1-ε)) := by
  have hroot := far_cutoff_root_bound hB hκ hε hfar
  have hd : 0 < 1-ε := sub_pos.mpr hε
  calc
    _ ≤ B/B^(1/(1-ε)) := div_le_div_of_nonneg_left hB.le (Real.rpow_pos_of_pos hB _) hroot
    _ = B^((1 : ℝ)-1/(1-ε)) := by rw [Real.rpow_sub hB,Real.rpow_one]
    _ = _ := by congr 1; field_simp [hd.ne'] <;> ring

/-- For a fixed positive a, the working construction's enlarged time is
below a*kappa throughout the far-cutoff branch, eventually uniformly in kappa. -/
theorem eventually_far_cutoff_time {a ε υ : ℝ} (ha : 0 < a) (hε : ε < 1)
    (hsep : (1-ε)*(1+υ) < 1) : ∀ᶠ B : ℝ in atTop, ∀ κ : ℝ,
      0 < κ → B ≤ κ^(1-ε) → B^(1+υ) ≤ a*κ := by
  have hd : 0 < 1-ε := sub_pos.mpr hε
  have hgap : 1+υ < 1/(1-ε) := (lt_div_iff₀ hd).mpr (by nlinarith only [hsep])
  filter_upwards [eventually_gt_atTop (0 : ℝ),eventually_const_mul_power_le hgap (1/a)] with B hB hpower
  intro κ hκ hfar
  have hroot := far_cutoff_root_bound hB hκ hε hfar
  have hh := mul_le_mul_of_nonneg_left (hpower.trans hroot) ha.le
  calc
    _ = a*((1/a)*B^(1+υ)) := by field_simp
    _ ≤ _ := hh

end
end StrongSilver
