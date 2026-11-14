-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.InitialPhaseBudget
import StrongSilver.OrdinaryPhaseParameters

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 1600000

theorem InitialPhaseBudget.ratio_power_bound {A μ b T κ B : ℝ} {h : List ℝ}
    (W : InitialPhaseBudget A μ b T κ B h) (hA : 0 < A) (hκA : κ ≤ A^((1003 : ℝ)/1000)) :
    κ/B ≤ A^((3 : ℝ)/1000) := by
  calc
    _ ≤ A^((1003 : ℝ)/1000)/B := div_le_div_of_nonneg_right hκA W.B_positive.le
    _ ≤ A^((1003 : ℝ)/1000)/A := div_le_div_of_nonneg_left
      (Real.rpow_pos_of_pos hA _).le hA W.cutoff_lower
    _ = A^((1003 : ℝ)/1000)/A^(1 : ℝ) := by rw [Real.rpow_one]
    _ = A^((1003 : ℝ)/1000-1) := (Real.rpow_sub hA _ _).symm
    _ = _ := by congr 1; norm_num

/-- A tracked initial phase satisfies the ordinary working construction
conditions. Its logarithmic negative-step bound follows from the uniform
initial budget, once the common cutoff is large. -/
theorem eventually_initial_tracked_parameters : ∀ᶠ A : ℝ in atTop,
    ∀ μ b T κ B P : ℝ, ∀ h : List ℝ, InitialPhaseBudget A μ b T κ B h →
      κ ≤ A^((1003 : ℝ)/1000) → A^((49 : ℝ)/50) ≤ P → P ≤ A^((199 : ℝ)/200) →
      OrdinaryPhaseParameters A μ b T P h := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),eventually_ge_atTop (Real.exp 500)] with A hA hAge
  intro μ b T κ B P h W hκA hPLower hPUpper
  have hA0 : 0 < A := zero_lt_one.trans hA
  have hlog : 500 ≤ Real.log A := by
    have hh := Real.log_le_log (Real.exp_pos 500) hAge
    simpa only [Real.log_exp] using hh
  have hApow : A^((499 : ℝ)/500) ≤ A := by
    have hh := Real.rpow_le_rpow_of_exponent_le hA.le (by norm_num : (499 : ℝ)/500 ≤ 1)
    simpa only [Real.rpow_one] using hh
  have hbκ : b ≤ κ := by linarith [W.pivot_upper,W.kappa_positive]
  have hmass := W.mass_pivot
  have hK := W.ratio_power_bound hA0 hκA
  exact {
    mu_positive := W.mu_positive
    b_lt_T := W.pivot_lt_time
    gap_cap := W.gap_cap
    pivot_lower := hApow.trans (W.cutoff_lower.trans W.pivot_lower)
    pivot_upper := hbκ.trans (hκA.trans (Real.rpow_le_rpow_of_exponent_le hA.le (by norm_num)))
    pad_lower := hPLower
    pad_upper := hPUpper
    cap_ratio := W.cap_ratio
    curvature := W.curvature
    mass_time := W.mass_time
    mass_pivot := hmass.trans hK
    mass_bound := W.mass.trans hκA
    time_bound := W.time_upper.trans (hκA.trans (Real.rpow_le_rpow_of_exponent_le hA.le (by norm_num)))
    negative_charge := by linarith [W.negative_charge]
  }

end
end StrongSilver
