-- SPDX-License-Identifier: GPL-3.0-only
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace StrongSilver
open Real

theorem norm_bound_from_aggregate {N M P m z α δ K H : ℝ}
    (hM : 0 ≤ M) (hP : 0 ≤ P) (hm : 0 ≤ m) (hz : 0 ≤ z) (hα : 0 ≤ α)
    (hδ : 0 ≤ δ) (hδα : δ ≤ α) (hK : K ≤ 1+α) (hH : H ≤ α*P)
    (hplane : M ≤ Real.exp z*(H+K*m)) (hsource : N ≤ (1+δ)*(M+P)) :
    N ≤ Real.exp (2*α+z)*(m+P) := by
  have hexp : 1 ≤ Real.exp z := Real.one_le_exp_iff.mpr hz
  have hKm := mul_le_mul_of_nonneg_right hK hm
  have hPe := mul_le_mul_of_nonneg_right hexp hP
  have hpoly : H+K*m+P ≤ (1+α)*(m+P) := by nlinarith only [hH,hKm]
  have hmul := mul_le_mul_of_nonneg_left hpoly (Real.exp_pos z).le
  have hQ : M+P ≤ (1+α)*Real.exp z*(m+P) := by nlinarith only [hplane,hPe,hmul]
  have hnormQ := mul_le_mul_of_nonneg_left hQ (show 0 ≤ 1+δ by linarith)
  have hαexp : 1+α ≤ Real.exp α := by linarith only [Real.add_one_le_exp α]
  have hδexp : 1+δ ≤ Real.exp α := by linarith only [hδα,hαexp]
  have hfactor := mul_le_mul hδexp hαexp (by linarith : 0 ≤ 1+α) (Real.exp_pos α).le
  have hB := mul_le_mul_of_nonneg_right hfactor (mul_nonneg (Real.exp_pos z).le (add_nonneg hm hP))
  have he : Real.exp α*Real.exp α*(Real.exp z*(m+P)) = Real.exp (2*α+z)*(m+P) := by
    rw [show 2*α+z = α+(α+z) by ring,Real.exp_add,Real.exp_add]
    ring
  rw [he] at hB
  nlinarith only [hsource,hnormQ,hB]

end StrongSilver
