-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.WorkingAnalyticBudget

namespace StrongSilver
open Real
noncomputable section
set_option maxHeartbeats 1000000

def workingAnalyticConstant : ℝ := 64*Real.exp 4

theorem workingAnalyticConstant_ge_one : 1 ≤ workingAnalyticConstant := by
  have he : 1 ≤ Real.exp 4 := Real.one_le_exp_iff.mpr (by norm_num)
  unfold workingAnalyticConstant
  linarith

namespace LocalPhaseCertificate
variable {A μ b T e : ℝ} {h : List ℝ} (L : LocalPhaseCertificate A μ b T e h)
include L

theorem working_norm_bound (hA : 1 ≤ A) (hlog : Real.log A ≤ A^((1 : ℝ)/20))
    (hAT : A/T ≤ 1/2) (hμT : μ*T ≤ 31/32)
    (hST : Scalar.SignedIntervals.positiveMass h/T ≤ 2)
    (hS : Scalar.SignedIntervals.positiveMass h ≤ A^((1003 : ℝ)/1000)) :
    ‖L.R‖ ≤ workingAnalyticConstant*A^((1003 : ℝ)/1000) := by
  have hm := transformedGapMaximum_nonnegative L.mu_positive h L.small_steps
  have hmax := L.working_gap_max_bound hAT hμT
  have hexp := Real.exp_le_exp.mpr (L.working_gap_exponent_bound hAT hμT hST)
  have hhead := L.planar.head_size_bound hlog
  have hradius : planarRadius A 0 ≤ 2 := by linarith [L.planar.head_radius_bound,L.planar.scale_le]
  have hradm := mul_le_mul_of_nonneg_right hradius hm
  have hpow : A^((1 : ℝ)/2) ≤ A^((1003 : ℝ)/1000) :=
    Real.rpow_le_rpow_of_exponent_le hA (by norm_num)
  have hp35 := mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 35)
  have hi : L.planar.right+L.planar.J 0+planarRadius A 0*transformedGapMaximum μ h ≤
      39*A^((1003 : ℝ)/1000) := by nlinarith only [hhead,hradm,hmax,hS,hp35]
  have hi0 : 0 ≤ L.planar.right+L.planar.J 0+planarRadius A 0*transformedGapMaximum μ h := by
    have hJ := L.planar.nonnegative 0 ⟨le_rfl,L.planar.angle_pos.le⟩
    exact add_nonneg (add_nonneg L.planar.right_pos.le hJ) (mul_nonneg (L.planar.radius_pos 0).le hm)
  have hp := mul_le_mul hexp hi hi0 (Real.exp_pos 4).le
  have hnorm := L.planar_start_norm_bound.trans hp
  unfold workingAnalyticConstant
  have hnonneg := mul_nonneg (Real.exp_pos 4).le (Real.rpow_nonneg (zero_le_one.trans hA) ((1003 : ℝ)/1000))
  nlinarith only [hnorm,hnonneg]

theorem working_terminalInner_bound (hA : 1 ≤ A) (hAT : A/T ≤ 1/2) (hμT : μ*T ≤ 31/32)
    (hST : Scalar.SignedIntervals.positiveMass h/T ≤ 2) :
    L.terminalInner ≤ A^(-(1 : ℝ)/5)*‖L.R‖+workingAnalyticConstant*A^((1 : ℝ)/2) := by
  have hp : A^((9 : ℝ)/20) ≤ A^((1 : ℝ)/2) := Real.rpow_le_rpow_of_exponent_le hA (by norm_num)
  have he := Real.exp_le_exp.mpr (L.working_gap_exponent_bound hAT hμT hST)
  have hm := mul_le_mul hp he (Real.exp_pos _).le (Real.rpow_nonneg (zero_le_one.trans hA) ((1 : ℝ)/2))
  have hn := L.terminalInner_bound
  change L.terminalInner ≤ A^(-(1 : ℝ)/5)*‖L.R‖+_ at hn
  unfold workingAnalyticConstant
  have hpos := mul_nonneg (Real.rpow_nonneg (zero_le_one.trans hA) ((1 : ℝ)/2)) (Real.exp_pos 4).le
  nlinarith only [hn,hm,hpos]

theorem working_q_bound (hAT : A/T ≤ 1/2) (hμT : μ*T ≤ 31/32)
    (hST : Scalar.SignedIntervals.positiveMass h/T ≤ 2) :
    1/workingAnalyticConstant ≤ quadraticMultiplier μ h*(1-μ*b) := by
  apply le_trans ?_ (L.working_q_lower hAT hμT hST)
  apply (one_div_le_one_div (by unfold workingAnalyticConstant; positivity : 0 < workingAnalyticConstant)
    (by positivity : (0 : ℝ) < 32*Real.exp 4)).mpr
  unfold workingAnalyticConstant
  nlinarith only [Real.exp_pos 4]

theorem working_growth_bound_constant (hA : 1 ≤ A) (hAT : A/T ≤ 1/2)
    (hST : Scalar.SignedIntervals.positiveMass h/T ≤ 2)
    (hSb : Scalar.SignedIntervals.positiveMass h/b ≤ A^((3 : ℝ)/1000)) :
    scalarRampGrowth T A b h ≤ workingAnalyticConstant*A^((3 : ℝ)/1000) := by
  have hh := L.working_growth_bound hA hAT hST hSb
  unfold workingAnalyticConstant
  have hp := mul_nonneg (Real.exp_pos 4).le (Real.rpow_nonneg (zero_le_one.trans hA) ((3 : ℝ)/1000))
  nlinarith only [hh,hp]

end LocalPhaseCertificate
end
end StrongSilver
