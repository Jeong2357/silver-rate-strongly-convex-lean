-- SPDX-License-Identifier: GPL-3.0-only
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace StrongSilver
set_option maxHeartbeats 1000000

theorem ratio_lower_of_source_squared_scale {U N E₀ E₁ L : ℝ}
    (hU : 0 < U) (hN : 0 < N) (hL : 0 < L) (hE₀ : 0 ≤ E₀) (hE : E₀ ≤ E₁)
    (hsource : N^2 ≤ L*U^2) : (E₀^2/U^2)/L ≤ E₁^2/N^2 := by
  have hE₁ : 0 ≤ E₁ := hE₀.trans hE
  have hEsq := (sq_le_sq₀ hE₀ hE₁).mpr hE
  have h1 := mul_le_mul_of_nonneg_left hsource (sq_nonneg E₀)
  have h2 := mul_le_mul_of_nonneg_right hEsq (mul_nonneg (sq_nonneg U) hL.le)
  rw [div_div]
  apply (div_le_div_iff₀ (mul_pos (sq_pos_of_pos hU) hL) (sq_pos_of_pos hN)).mpr
  nlinarith only [h1,h2]

theorem ratio_lower_of_source_scale {U N E₀ E₁ C : ℝ}
    (hU : 0 < U) (hN : 0 < N) (hC : 0 < C) (hE₀ : 0 ≤ E₀) (hE : E₀ ≤ E₁)
    (hsource : N ≤ C*U) : (E₀^2/U^2)/C^2 ≤ E₁^2/N^2 := by
  have hsq := (sq_le_sq₀ hN.le (mul_pos hC hU).le).mpr hsource
  rw [mul_pow] at hsq
  exact ratio_lower_of_source_squared_scale hU hN (sq_pos_of_pos hC) hE₀ hE hsq

end StrongSilver
