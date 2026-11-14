-- SPDX-License-Identifier: GPL-3.0-only
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace StrongSilver
open Real
set_option maxHeartbeats 1200000

/-- The terminal prefix maximum cancels the M^(3/2) squared-entry price.
Here m=sqrt(M), so all comparisons are polynomial inequalities. -/
theorem terminal_ratio_of_entry_bound {m V F L N E t : ℝ} (hm : 1 ≤ m) (hV : 0 < V)
    (hF : 0 < F) (hL : 0 < L) (hN : 0 < N)
    (hentry : N^2 ≤ L*m^3*V^2*F^2) (hterminal : m^2*V*Real.exp (-2*t) ≤ E) :
    Real.exp (-4*t)/(L*F^2) ≤ E^2/N^2 := by
  have hm0 : 0 < m := zero_lt_one.trans_le hm
  have hE : 0 < E := (by positivity : 0 < m^2*V*Real.exp (-2*t)).trans_le hterminal
  have hEsq := (sq_le_sq₀ (by positivity : 0 ≤ m^2*V*Real.exp (-2*t)) hE.le).mpr hterminal
  have hm34 := mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ m^3)
  have hM := mul_le_mul_of_nonneg_right hm34 (by positivity : 0 ≤ V^2*(Real.exp (-2*t))^2)
  have hlow : m^3*V^2*(Real.exp (-2*t))^2 ≤ E^2 := by nlinarith only [hEsq,hM]
  have hlowScale := mul_le_mul_of_nonneg_left hlow (by positivity : 0 ≤ L*F^2)
  have hentryScale := mul_le_mul_of_nonneg_right hentry (sq_nonneg (Real.exp (-2*t)))
  apply (div_le_div_iff₀ (mul_pos hL (sq_pos_of_pos hF)) (sq_pos_of_pos hN)).mpr
  have he : Real.exp (-4*t) = (Real.exp (-2*t))^2 := by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  rw [he]
  nlinarith only [hlowScale,hentryScale]

end StrongSilver
