-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PowerMargins

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 1200000

theorem eventually_exceptional_norm_bound : ∀ᶠ A : ℝ in atTop,
    ∀ N U Z H R : ℝ, 0 ≤ N → 0 ≤ U → U ≤ R → Z ≤ 2*R → H ≤ 2*R →
      N^2 ≤ A^(19 : ℝ)*(U^2+U*Z+U*H) → N ≤ A^(11 : ℝ)*R := by
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    eventually_const_mul_power_le (by norm_num : (19 : ℝ) < 22) 5] with A hA hpow
  intro N U Z H R hN hU hUR hZ hH hNsq
  have hR : 0 ≤ R := hU.trans hUR
  have hsq : U^2 ≤ R^2 := (sq_le_sq₀ hU hR).mpr hUR
  have hUZ := mul_le_mul_of_nonneg_left hZ hU
  have hUH := mul_le_mul_of_nonneg_left hH hU
  have hRUR := mul_le_mul_of_nonneg_right hUR hR
  have hsum : U^2+U*Z+U*H ≤ 5*R^2 := by nlinarith only [hsq,hUZ,hUH,hRUR]
  have h1 := mul_le_mul_of_nonneg_left hsum (Real.rpow_pos_of_pos hA (19 : ℝ)).le
  have h2 := mul_le_mul_of_nonneg_right hpow (sq_nonneg R)
  have hsquare : (A^(11 : ℝ)*R)^2 = A^(22 : ℝ)*R^2 := by
    rw [mul_pow,← Real.rpow_mul_natCast hA.le]
    norm_num
  have hfinal : N^2 ≤ (A^(11 : ℝ)*R)^2 := by
    rw [hsquare]
    nlinarith only [hNsq,h1,h2]
  exact (sq_le_sq₀ hN (mul_nonneg (Real.rpow_pos_of_pos hA _).le hR)).mp hfinal

end
end StrongSilver
