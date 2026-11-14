-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.WorkingPaddingLinear

namespace StrongSilver.LocalPhaseCertificate
open Real
noncomputable section
variable {A μ b T e : ℝ} {h : List ℝ} (L : LocalPhaseCertificate A μ b T e h)
include L
set_option maxHeartbeats 1400000

theorem working_scalar_scale_ge_one {P : ℝ} (hP : A^((49 : ℝ)/50) ≤ P)
    (he : e^2 = A^(-(3 : ℝ)/25)*T*(‖L.R‖+P)) : 1 ≤ e := by
  have hA : 1 ≤ A := L.planar.large.le
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  have hT : 1 ≤ T := by linarith [L.b_large,L.b_lt_T]
  have hQ : A^((49 : ℝ)/50) ≤ ‖L.R‖+P := by linarith only [hP,norm_nonneg L.R]
  have hTQ : A^((49 : ℝ)/50) ≤ T*(‖L.R‖+P) :=
    (by simpa only [one_mul] using mul_le_mul hT hQ (Real.rpow_pos_of_pos hA0 ((49 : ℝ)/50)).le L.T_positive.le)
  have hh := mul_le_mul_of_nonneg_left hTQ (Real.rpow_pos_of_pos hA0 (-(3 : ℝ)/25)).le
  have hp : A^(-(3 : ℝ)/25)*A^((49 : ℝ)/50) = A^((43 : ℝ)/50) := by
    rw [← Real.rpow_add hA0]; congr 1; norm_num
  rw [hp,← mul_assoc,← he] at hh
  have hpow : 1 ≤ A^((43 : ℝ)/50) := Real.one_le_rpow hA (by norm_num)
  nlinarith only [hh,hpow,L.e_positive]

theorem scalar_start_lower_simple (hE : negativeLogSum h T ≤ (1/250)*Real.log A) :
    e/(2*A) ≤ L.scalar.x := by
  have hA : 1 ≤ A := L.planar.large.le
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  have hExp : 1/A ≤ Real.exp (-negativeLogSum h T) := by
    rw [one_div,← Real.exp_log hA0,← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    nlinarith only [hE,Real.log_nonneg hA]
  have hh := mul_le_mul_of_nonneg_left hExp (div_nonneg L.e_positive.le (by norm_num : (0 : ℝ) ≤ 2))
  have hlower := (L.scalar.estimates 0 (by omega)).1
  simp only [List.take_zero,iterate_nil] at hlower
  have heq : (e/2)*(1/A) = e/(2*A) := by ring
  rw [heq] at hh
  exact hh.trans hlower

end
end StrongSilver.LocalPhaseCertificate
