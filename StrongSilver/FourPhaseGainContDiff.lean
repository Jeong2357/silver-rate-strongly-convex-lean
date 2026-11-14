-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseGainIdentities
import StrongSilver.ContDiffPairBoxBound
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace StrongSilver.FourPhase
noncomputable section
set_option maxHeartbeats 2800000

@[fun_prop] theorem contDiff_t0 : ContDiff ℝ 1 t0 := by unfold t0; fun_prop
@[fun_prop] theorem contDiff_t1 : ContDiff ℝ 1 t1 := by unfold t1; fun_prop
@[fun_prop] theorem contDiff_t2 : ContDiff ℝ 1 t2 := by unfold t2; fun_prop
@[fun_prop] theorem contDiff_totalTime : ContDiff ℝ 1 totalTime := by unfold totalTime; fun_prop
@[fun_prop] theorem contDiff_leftMass : ContDiff ℝ 1 leftMass := by unfold leftMass; fun_prop
@[fun_prop] theorem contDiff_rightMass : ContDiff ℝ 1 rightMass := by unfold rightMass; fun_prop
@[fun_prop] theorem contDiff_totalMass : ContDiff ℝ 1 totalMass := by unfold totalMass; fun_prop

theorem coordinate_contDiff (i : Fin 8) : ContDiffAt ℝ 1 (fun x : Shape => x i) reference := by fun_prop

@[fun_prop] theorem contDiffAt_gain_reference : ContDiffAt ℝ 1 gain reference := by
  have hL : leftMass reference ≠ 0 := by rw [leftMass_reference]; exact rho_positive.ne'
  have hR : rightMass reference ≠ 0 := by rw [rightMass_reference]; exact rho_positive.ne'
  have hM : totalMass reference ≠ 0 := by rw [totalMass_reference]; exact pow_ne_zero _ rho_positive.ne'
  have hk : reference 5 ≠ 0 := by norm_num
  unfold gain
  apply ContDiffAt.log
  · simp only [div_eq_mul_inv]
    fun_prop (disch := aesop)
  · exact div_ne_zero (mul_ne_zero hk hM) (mul_ne_zero hL hR)

@[fun_prop] theorem contDiffAt_gainLeft_reference : ContDiffAt ℝ 1 gainLeft reference := by
  have hL : leftMass reference ≠ 0 := by rw [leftMass_reference]; exact rho_positive.ne'
  have hk : reference 4 ≠ 0 := by rw [reference_k0]; exact inv_ne_zero rho_positive.ne'
  have h0 : reference 0 ≠ 0 := by norm_num
  have h1 : reference 1 ≠ 0 := by norm_num
  unfold gainLeft
  apply ContDiffAt.log
  · simp only [div_eq_mul_inv]
    fun_prop (disch := aesop)
  · exact div_ne_zero (mul_ne_zero hk hL) (mul_ne_zero h0 h1)

@[fun_prop] theorem contDiffAt_gainRight_reference : ContDiffAt ℝ 1 gainRight reference := by
  have hR : rightMass reference ≠ 0 := by rw [rightMass_reference]; exact rho_positive.ne'
  have hk : reference 6 ≠ 0 := by rw [reference_k2]; exact inv_ne_zero rho_positive.ne'
  have h2 : reference 2 ≠ 0 := by norm_num
  have h3 : reference 3 ≠ 0 := by norm_num
  unfold gainRight
  apply ContDiffAt.log
  · simp only [div_eq_mul_inv]
    fun_prop (disch := aesop)
  · exact div_ne_zero (mul_ne_zero hk hR) (mul_ne_zero h2 h3)

@[fun_prop] theorem contDiffAt_gainCoefficient_reference : ContDiffAt ℝ 1 gainCoefficient reference := by
  have hden : reference 5*totalTime reference ≠ 0 := by
    rw [reference_k1,totalTime_reference]
    exact mul_ne_zero (by norm_num) (mul_ne_zero (by norm_num) rho_positive.ne')
  unfold gainCoefficient
  simp only [div_eq_mul_inv]
  fun_prop (disch := assumption)

end
end StrongSilver.FourPhase
