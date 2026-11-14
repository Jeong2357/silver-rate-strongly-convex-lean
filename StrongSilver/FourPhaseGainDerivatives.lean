-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseGainIdentities
import StrongSilver.DifferentiableBoxBound
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace StrongSilver.FourPhase
noncomputable section
set_option maxHeartbeats 2800000

@[fun_prop] theorem differentiable_t0 : Differentiable ℝ t0 := by unfold t0; fun_prop
@[fun_prop] theorem differentiable_t1 : Differentiable ℝ t1 := by unfold t1; fun_prop
@[fun_prop] theorem differentiable_t2 : Differentiable ℝ t2 := by unfold t2; fun_prop
@[fun_prop] theorem differentiable_totalTime : Differentiable ℝ totalTime := by unfold totalTime; fun_prop
@[fun_prop] theorem differentiable_leftMass : Differentiable ℝ leftMass := by unfold leftMass; fun_prop
@[fun_prop] theorem differentiable_rightMass : Differentiable ℝ rightMass := by unfold rightMass; fun_prop
@[fun_prop] theorem differentiable_totalMass : Differentiable ℝ totalMass := by unfold totalMass; fun_prop

theorem coordinate_derivative (i : Fin 8) : DifferentiableAt ℝ (fun x : Shape => x i) reference := by fun_prop

@[fun_prop] theorem differentiableAt_gain_reference : DifferentiableAt ℝ gain reference := by
  have hL : leftMass reference ≠ 0 := by rw [leftMass_reference]; exact rho_positive.ne'
  have hR : rightMass reference ≠ 0 := by rw [rightMass_reference]; exact rho_positive.ne'
  have hM : totalMass reference ≠ 0 := by rw [totalMass_reference]; exact pow_ne_zero _ rho_positive.ne'
  have hk : reference 5 ≠ 0 := by norm_num
  unfold gain
  apply DifferentiableAt.log
  · simp only [div_eq_mul_inv]
    fun_prop (disch := aesop)
  · exact div_ne_zero (mul_ne_zero hk hM) (mul_ne_zero hL hR)

@[fun_prop] theorem differentiableAt_gainLeft_reference : DifferentiableAt ℝ gainLeft reference := by
  have hL : leftMass reference ≠ 0 := by rw [leftMass_reference]; exact rho_positive.ne'
  have hk : reference 4 ≠ 0 := by rw [reference_k0]; exact inv_ne_zero rho_positive.ne'
  have h0 : reference 0 ≠ 0 := by norm_num
  have h1 : reference 1 ≠ 0 := by norm_num
  unfold gainLeft
  apply DifferentiableAt.log
  · simp only [div_eq_mul_inv]
    fun_prop (disch := aesop)
  · exact div_ne_zero (mul_ne_zero hk hL) (mul_ne_zero h0 h1)

@[fun_prop] theorem differentiableAt_gainRight_reference : DifferentiableAt ℝ gainRight reference := by
  have hR : rightMass reference ≠ 0 := by rw [rightMass_reference]; exact rho_positive.ne'
  have hk : reference 6 ≠ 0 := by rw [reference_k2]; exact inv_ne_zero rho_positive.ne'
  have h2 : reference 2 ≠ 0 := by norm_num
  have h3 : reference 3 ≠ 0 := by norm_num
  unfold gainRight
  apply DifferentiableAt.log
  · simp only [div_eq_mul_inv]
    fun_prop (disch := aesop)
  · exact div_ne_zero (mul_ne_zero hk hR) (mul_ne_zero h2 h3)

@[fun_prop] theorem differentiableAt_gainCoefficient_reference : DifferentiableAt ℝ gainCoefficient reference := by
  have hden : reference 5*totalTime reference ≠ 0 := by
    rw [reference_k1,totalTime_reference]
    exact mul_ne_zero (by norm_num) (mul_ne_zero (by norm_num) rho_positive.ne')
  unfold gainCoefficient
  simp only [div_eq_mul_inv]
  fun_prop (disch := assumption)

end
end StrongSilver.FourPhase
