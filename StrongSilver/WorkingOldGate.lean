-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.WorkingNewGate

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 1600000

namespace LocalPhaseCertificate
variable {A μ b T e : ℝ} {h : List ℝ} (L : LocalPhaseCertificate A μ b T e h)

theorem terminalGate_le_linear : L.terminalGate ≤ 2*L.terminalInner*Real.exp (negativeLogSum h T)/b := by
  have hb : 0 < b-1 := by linarith [L.b_large]
  have hEn : 0 < ‖L.path.x (Fin.last _)‖^2 := sq_pos_of_pos (norm_pos_iff.mpr L.endpoint_ne_zero)
  have hE : (b-1)^2 ≤ ‖L.path.x (Fin.last _)‖^2 := by
    nlinarith only [L.endpoint_norm_lower,norm_nonneg (L.path.x (Fin.last _)),hb]
  have hJ : 0 ≤ L.terminalInner*Real.exp (negativeLogSum h T) :=
    mul_nonneg L.terminalInner_nonnegative (Real.exp_pos _).le
  have hfirst : L.terminalGate ≤ (L.terminalInner*Real.exp (negativeLogSum h T))/(b-1) := by
    unfold terminalGate
    apply (div_le_div_iff₀ hEn hb).mpr
    have hm := mul_le_mul_of_nonneg_left hE hJ
    nlinarith only [hm]
  apply hfirst.trans
  apply (div_le_div_iff₀ hb L.b_positive).mpr
  have hp := mul_nonneg hJ (show 0 ≤ b-2 by linarith [L.b_large])
  nlinarith only [hp]

end LocalPhaseCertificate

theorem eventually_working_old_gate : ∀ᶠ A : ℝ in atTop,
    ∀ μ b T e : ℝ, ∀ h : List ℝ, ∀ L : LocalPhaseCertificate A μ b T e h,
      Real.log A ≤ A^((1 : ℝ)/20) → A/T ≤ 1/2 → μ*T ≤ 31/32 →
      Scalar.SignedIntervals.positiveMass h/T ≤ 2 →
      Scalar.SignedIntervals.positiveMass h ≤ A^((1003 : ℝ)/1000) →
      A^((499 : ℝ)/500) ≤ b → negativeLogSum h T ≤ (1/250)*Real.log A →
      L.terminalGate ≤ workingGateFraction A := by
  let K := workingAnalyticConstant
  have hK : 0 ≤ K := zero_le_one.trans workingAnalyticConstant_ge_one
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    eventually_const_mul_power_le (by norm_num : -(191 : ℝ)/1000 < -(67 : ℝ)/500) (4*K)]
    with A hA hmargin
  intro μ b T e h L hlog hAT hμT hST hS hb hE
  have hA0 := zero_lt_one.trans hA
  have hM := L.working_norm_bound hA.le hlog hAT hμT hST hS
  have hJ0 := L.working_terminalInner_bound hA.le hAT hμT hST
  have hMp := mul_le_mul_of_nonneg_left hM (Real.rpow_pos_of_pos hA0 (-(1 : ℝ)/5)).le
  have hp : A^((1 : ℝ)/2) ≤ A^((803 : ℝ)/1000) := Real.rpow_le_rpow_of_exponent_le hA.le (by norm_num)
  have hpK := mul_le_mul_of_nonneg_left hp hK
  have hpow : A^(-(1 : ℝ)/5)*A^((1003 : ℝ)/1000) = A^((803 : ℝ)/1000) := by
    rw [← Real.rpow_add hA0]; congr 1; norm_num
  have hJ : L.terminalInner ≤ 2*K*A^((803 : ℝ)/1000) := by
    have heq : A^(-(1 : ℝ)/5)*(K*A^((1003 : ℝ)/1000)) = K*A^((803 : ℝ)/1000) := by rw [← hpow]; ring
    rw [heq] at hMp
    nlinarith only [hJ0,hMp,hpK]
  have hexp : Real.exp (negativeLogSum h T) ≤ A^((1 : ℝ)/250) := by
    rw [Real.rpow_def_of_pos hA0]
    exact Real.exp_le_exp.mpr (by nlinarith only [hE])
  have hprod := mul_le_mul hJ hexp (Real.exp_pos _).le
    (mul_nonneg (by positivity : 0 ≤ 2*K) (Real.rpow_pos_of_pos hA0 _).le)
  have hp2 : A^((803 : ℝ)/1000)*A^((1 : ℝ)/250) = A^((807 : ℝ)/1000) := by
    rw [← Real.rpow_add hA0]; congr 1; norm_num
  have hJprod : L.terminalInner*Real.exp (negativeLogSum h T) ≤ 2*K*A^((807 : ℝ)/1000) := by
    have heq : (2*K*A^((803 : ℝ)/1000))*A^((1 : ℝ)/250) = 2*K*A^((807 : ℝ)/1000) := by rw [← hp2]; ring
    rwa [heq] at hprod
  have hfrac : A^((807 : ℝ)/1000)/b ≤ A^(-(191 : ℝ)/1000) := by
    have hh : A^((807 : ℝ)/1000)/b ≤ A^((807 : ℝ)/1000)/A^((499 : ℝ)/500) := by gcongr
    rw [← Real.rpow_sub hA0] at hh
    convert hh using 1 <;> norm_num
  have hdiv := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hJprod (by norm_num : (0 : ℝ) ≤ 2)) L.b_positive.le
  have hscale := mul_le_mul_of_nonneg_left hfrac (show 0 ≤ 4*K by positivity)
  have hlin := L.terminalGate_le_linear
  unfold workingGateFraction
  simp only [div_eq_mul_inv] at hdiv hscale hlin
  nlinarith only [hdiv,hscale,hlin,hmargin]

end
end StrongSilver
