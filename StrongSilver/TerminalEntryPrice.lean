-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.TerminalRatioBound

namespace StrongSilver
open Real
set_option maxHeartbeats 1600000

theorem terminal_entry_price {m V F C L U Z H N : ℝ} (hm : 1 ≤ m) (hV : 0 < V)
    (hF : 1 ≤ F) (hC : 1 ≤ C) (hL : 0 ≤ L) (hU : 0 ≤ U)
    (hUR : U ≤ C*m*V*F) (hZ : Z ≤ C*m*V*F+m^2*V) (hH : H ≤ C*m*V*F)
    (hN : N^2 ≤ L*(U^2+U*Z+U*H)) :
    N^2 ≤ (4*L*C^2)*m^3*V^2*F^2 := by
  let R := C*m*V*F
  have hm0 : 0 < m := zero_lt_one.trans_le hm
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have hF0 : 0 < F := zero_lt_one.trans_le hF
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hCF := mul_le_mul hC hF (by norm_num : (0 : ℝ) ≤ 1) hC0.le
  have hRbase : m*V ≤ R := by
    have hh := mul_le_mul_of_nonneg_right hCF (mul_nonneg hm0.le hV.le)
    dsimp only [R]
    nlinarith only [hh]
  have hM := mul_le_mul_of_nonneg_left hRbase hm0.le
  have hmR := mul_le_mul_of_nonneg_right hm hR
  have hZR : Z ≤ 2*m*R := by nlinarith only [hZ,hM,hmR]
  have hsq := (sq_le_sq₀ hU hR).mpr hUR
  have hUZ := mul_le_mul_of_nonneg_left hZR hU
  have hH' := mul_le_mul_of_nonneg_left hH hU
  have hURR := mul_le_mul_of_nonneg_right hUR hR
  have hURmR := mul_le_mul_of_nonneg_right hUR (by positivity : 0 ≤ 2*m*R)
  have hmR2 := mul_le_mul_of_nonneg_right hm (sq_nonneg R)
  have hsum : U^2+U*Z+U*H ≤ 4*m*R^2 := by
    nlinarith only [hsq,hUZ,hH',hURR,hURmR,hmR2]
  have hscale := mul_le_mul_of_nonneg_left hsum hL
  apply hN.trans (hscale.trans_eq ?_)
  dsimp only [R]
  ring

end StrongSilver
