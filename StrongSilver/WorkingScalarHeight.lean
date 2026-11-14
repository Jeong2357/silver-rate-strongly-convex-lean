-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PowerNormalization

namespace StrongSilver
open Real
noncomputable section
set_option maxHeartbeats 1000000

theorem working_scalar_height_lower {A μ T E e Q : ℝ} (hA : 0 < A) (hT : 0 < T)
    (hμT : μ*T ≤ 31/32) (hE : E ≤ (1/250)*Real.log A)
    (he : e^2 = A^(-(3 : ℝ)/25)*T*Q) :
    ((1 : ℝ)/1024)*A^(-(16 : ℝ)/125)*Q ≤ ((1/T-μ)/32)*Real.exp (-2*E)*e^2 := by
  have hcoef : 1/(1024*T) ≤ (1/T-μ)/32 := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hT)).mpr
    have hx : ((1/T-μ)/32)*(1024*T) = 32*(1-μ*T) := by field_simp [hT.ne']; ring
    rw [hx]
    nlinarith only [hμT]
  have hcoef0 : 0 ≤ (1/T-μ)/32 := (by positivity : 0 ≤ 1/(1024*T)).trans hcoef
  have hexp : A^(-(1 : ℝ)/125) ≤ Real.exp (-2*E) := by
    rw [Real.rpow_def_of_pos hA]
    apply Real.exp_le_exp.mpr
    nlinarith only [hE]
  have hp := mul_le_mul hcoef hexp (Real.rpow_pos_of_pos hA (-(1 : ℝ)/125)).le hcoef0
  have hmul := mul_le_mul_of_nonneg_right hp (sq_nonneg e)
  have hpower : A^(-(1 : ℝ)/125)*A^(-(3 : ℝ)/25) = A^(-(16 : ℝ)/125) := by
    rw [← Real.rpow_add hA]
    congr 1
    norm_num
  have heq : (1/(1024*T)*A^(-(1 : ℝ)/125))*(A^(-(3 : ℝ)/25)*T*Q) =
      ((1 : ℝ)/1024)*A^(-(16 : ℝ)/125)*Q := by
    rw [← hpower]
    field_simp [hT.ne']
    <;> ring
  rw [he,heq] at hmul
  simpa only [he] using hmul

end
end StrongSilver
