-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PowerMargins
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 2000000

theorem eventually_sqrt_affine_le_linear {ε : ℝ} (hε : 0 < ε) (C D : ℝ) :
    ∀ᶠ u : ℝ in atTop, C*Real.sqrt u+D ≤ ε*u := by
  filter_upwards [eventually_const_mul_power_le (by norm_num : (1:ℝ)/2 < 1) (2*C/ε),
    eventually_const_mul_power_le (by norm_num : (0:ℝ) < 1) (2*D/ε)] with u h1 h2
  rw [← Real.sqrt_eq_rpow] at h1
  simp only [Real.rpow_one,Real.rpow_zero,mul_one] at h1 h2
  have hhalf : 0 ≤ ε/2 := by positivity
  have hm1 := mul_le_mul_of_nonneg_left h1 hhalf
  have hm2 := mul_le_mul_of_nonneg_left h2 hhalf
  have he1 : ε/2*((2*C/ε)*Real.sqrt u) = C*Real.sqrt u := by field_simp <;> ring
  have he2 : ε/2*(2*D/ε) = D := by field_simp <;> ring
  rw [he1] at hm1
  rw [he2] at hm2
  linarith only [hm1,hm2]

end
end StrongSilver
