-- SPDX-License-Identifier: GPL-3.0-only
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace StrongSilver
open Real
set_option maxHeartbeats 1000000

theorem ratio_lower_of_exponential_entry {V N E L u : ℝ} (hV : 0 < V) (hN : 0 < N) (hL : 0 < L)
    (hE : V ≤ E) (hsource : N^2 ≤ L*(Real.exp u*V)^2) :
    Real.exp (-2*u)/L ≤ E^2/N^2 := by
  have hE0 : 0 < E := hV.trans_le hE
  have hEsq := (sq_le_sq₀ hV.le hE0.le).mpr hE
  have hscale := mul_le_mul_of_nonneg_left hsource (Real.exp_pos (-2*u)).le
  have hcancel : Real.exp (-2*u)*(Real.exp u)^2 = 1 := by
    rw [pow_two,← mul_assoc,← Real.exp_add,← Real.exp_add]
    rw [show -2*u+u+u = 0 by ring,Real.exp_zero]
  have heq : Real.exp (-2*u)*(L*(Real.exp u*V)^2) = L*V^2 := by
    calc
      _ = L*V^2*(Real.exp (-2*u)*(Real.exp u)^2) := by ring
      _ = _ := by rw [hcancel,mul_one]
  rw [heq] at hscale
  have hEscale := mul_le_mul_of_nonneg_left hEsq hL.le
  apply (div_le_div_iff₀ hL (sq_pos_of_pos hN)).mpr
  nlinarith only [hscale,hEscale]

end StrongSilver
