-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.InitialPhaseGeometry
import StrongSilver.WorkingOldGate

namespace StrongSilver
open Real
noncomputable section

def initialOldGateConstant : ℝ := 18*Real.exp 2*initialPlaneConstant
def initialOldGate (A κ B : ℝ) : ℝ := initialOldGateConstant*(planarEpsilon A*κ+A^((1 : ℝ)/2))/B

theorem initialOldGateConstant_positive : 0 < initialOldGateConstant := by
  have := initialPlaneConstant_positive
  unfold initialOldGateConstant
  positivity

namespace InitialPhaseBudget
variable {A μ b T κ B e : ℝ} {h : List ℝ} (W : InitialPhaseBudget A μ b T κ B h)
    (L : LocalPhaseCertificate A μ b T e h)
include W L
set_option maxHeartbeats 1800000

theorem old_gate : L.terminalGate ≤ initialOldGate A κ B := by
  have hA : 1 ≤ A := L.planar.large.le
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  have hCp := initialPlaneConstant_positive
  have hM := mul_le_mul_of_nonneg_left (W.plane_start L) L.planar.epsilon_pos.le
  have hexp := Real.exp_le_exp.mpr (L.working_gap_exponent_bound W.cap_ratio W.curvature W.mass_time)
  have hE := mul_le_mul_of_nonneg_left hexp (by positivity : 0 ≤ 32*A^((9 : ℝ)/20))
  have hpower : A^((9 : ℝ)/20) ≤ A^((1 : ℝ)/2) := Real.rpow_le_rpow_of_exponent_le hA (by norm_num)
  have hE2 := mul_le_mul_of_nonneg_left hpower (by positivity : 0 ≤ 32*Real.exp 4)
  have hJ := L.terminalInner_bound
  have hterm0 : 0 ≤ planarEpsilon A*κ := mul_nonneg L.planar.epsilon_pos.le W.kappa_positive.le
  have hpow0 := (Real.rpow_pos_of_pos hA0 ((1 : ℝ)/2)).le
  have hCterm := mul_nonneg hCp.le hterm0
  have hCpow := mul_nonneg hCp.le hpow0
  have hJ' : L.terminalInner ≤ 9*initialPlaneConstant*(planarEpsilon A*κ+A^((1 : ℝ)/2)) := by
    unfold initialPlaneConstant at hM hCterm hCpow ⊢
    nlinarith only [hJ,hM,hE,hE2,hCterm,hCpow]
  have hExp := Real.exp_le_exp.mpr W.negative_charge
  have hright0 : 0 ≤ 9*initialPlaneConstant*(planarEpsilon A*κ+A^((1 : ℝ)/2)) := by positivity
  have hprod := mul_le_mul hJ' hExp (Real.exp_pos _).le hright0
  have hdiv := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 2)) L.b_positive.le
  have hCold := initialOldGateConstant_positive
  have hden := div_le_div_of_nonneg_left (by positivity : 0 ≤ initialOldGateConstant*(planarEpsilon A*κ+A^((1 : ℝ)/2)))
    W.B_positive W.pivot_lower
  have hlin := L.terminalGate_le_linear
  have hdiv' : 2*L.terminalInner*Real.exp (negativeLogSum h T)/b ≤
      initialOldGateConstant*(planarEpsilon A*κ+A^((1 : ℝ)/2))/b := by
    calc
      _ = 2*(L.terminalInner*Real.exp (negativeLogSum h T))/b := by ring
      _ ≤ 2*(9*initialPlaneConstant*(planarEpsilon A*κ+A^((1 : ℝ)/2))*Real.exp 2)/b := hdiv
      _ = _ := by unfold initialOldGateConstant; ring
  exact hlin.trans (hdiv'.trans hden)

end InitialPhaseBudget
end
end StrongSilver
