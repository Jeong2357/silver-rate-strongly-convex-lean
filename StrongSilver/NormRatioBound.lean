-- SPDX-License-Identifier: GPL-3.0-only
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace StrongSilver
open Real

theorem ratio_lower_of_norm_upper {N E B M z : ℝ} (hN : 0 < N) (hM : 0 < M)
    (hB : 0 ≤ B) (hE : B ≤ E) (hupper : N ≤ Real.exp z*M) :
    (B/M)*Real.exp (-z) ≤ E/N := by
  apply (le_div_iff₀ hN).mpr
  have hfactor : 0 ≤ (B/M)*Real.exp (-z) := mul_nonneg (div_nonneg hB hM.le) (Real.exp_pos _).le
  have hm := mul_le_mul_of_nonneg_left hupper hfactor
  have he : ((B/M)*Real.exp (-z))*(Real.exp z*M) = B := by
    have hexp : Real.exp (-z)*Real.exp z = 1 := by rw [← Real.exp_add,neg_add_cancel,Real.exp_zero]
    calc
      _ = (B/M)*(Real.exp (-z)*Real.exp z)*M := by ring
      _ = B := by rw [hexp,mul_one,div_mul_cancel₀ _ hM.ne']
  rw [he] at hm
  exact hm.trans hE

end StrongSilver
