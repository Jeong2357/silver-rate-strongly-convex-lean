-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.WorkingAssembly

namespace StrongSilver
open Real
noncomputable section
set_option maxHeartbeats 1600000

theorem OrdinaryPhaseParameters.padded_ratio_positive {A μ b T P : ℝ} {h : List ℝ}
    (W : OrdinaryPhaseParameters A μ b T P h) (hA : 1 < A) : 0 < (b-P)/(transformedGapMaximum μ h+P) := by
  have hA0 := zero_lt_one.trans hA
  have hP := (Real.rpow_pos_of_pos hA0 _).trans_le W.pad_lower
  have hm := transformedGapMaximum_nonnegative W.mu_positive h (W.small_steps hA0)
  exact div_pos (sub_pos.mpr (W.pad_lt_pivot hA)) (add_pos_of_nonneg_of_pos hm hP)

theorem OrdinaryPhaseParameters.log_reference_factor {A μ b T P : ℝ} {h : List ℝ}
    (W : OrdinaryPhaseParameters A μ b T P h) (hA : 1 < A) :
    Real.log (ordinaryReferenceFactor A μ b P h) =
      Real.log ((b-P)/(transformedGapMaximum μ h+P))-(1200/Real.log A+μ*transformedGapMaximum μ h) := by
  rw [ordinaryReferenceFactor,Real.log_mul (W.padded_ratio_positive hA).ne' (Real.exp_ne_zero _),Real.log_exp]
  ring

theorem workingBlockFactor_positive {A : ℝ} (hA : 0 < A) (μ : ℝ) (I : List ℝ) :
    0 < workingBlockFactor A μ I := by
  have hs := smallPositiveSum_nonneg μ I
  unfold workingBlockFactor
  positivity

theorem log_workingBlockFactor {A : ℝ} (hA : 0 < A) (μ : ℝ) (I : List ℝ) :
    Real.log (workingBlockFactor A μ I) = 25*Real.log A+inverseCharge μ I+Real.log (1+smallPositiveSum μ I) := by
  have hs : 0 < 1+smallPositiveSum μ I := by linarith only [smallPositiveSum_nonneg μ I]
  rw [workingBlockFactor,Real.log_mul (by positivity) hs.ne',
    Real.log_mul (by positivity) (Real.exp_ne_zero _),Real.log_rpow hA,Real.log_exp]

theorem workingTerminalRate_positive {A : ℝ} (hA : 0 < A) (μ : ℝ) (I t : List ℝ) :
    0 < workingTerminalRate A μ I t := by
  have hs := smallPositiveSum_nonneg μ I
  unfold workingTerminalRate
  positivity

theorem log_workingTerminalRate {A : ℝ} (hA : 0 < A) (μ : ℝ) (I t : List ℝ) :
    Real.log (workingTerminalRate A μ I t) =
      -4*(μ*Scalar.SignedIntervals.positiveMass t)-Real.log (4*A^(19 : ℝ)*(1200000 : ℝ)^2)-
        2*(inverseCharge μ I+Real.log (1+smallPositiveSum μ I)) := by
  have hs : 0 < 1+smallPositiveSum μ I := by linarith only [smallPositiveSum_nonneg μ I]
  rw [workingTerminalRate,Real.log_div (Real.exp_ne_zero _) (by positivity),Real.log_exp,
    Real.log_mul (by positivity) (by positivity),Real.log_pow,
    Real.log_mul (Real.exp_ne_zero _) hs.ne',Real.log_exp]
  norm_num
  ring

theorem workingNoConnectorRate_positive {A : ℝ} (hA : 0 < A) (μ : ℝ) (I t : List ℝ) :
    0 < workingNoConnectorRate A μ I t := by
  unfold workingNoConnectorRate
  positivity

theorem log_workingNoConnectorRate {A : ℝ} (hA : 0 < A) (μ : ℝ) (I t : List ℝ) :
    Real.log (workingNoConnectorRate A μ I t) =
      -2*inverseCharge μ I-4*μ*Scalar.SignedIntervals.positiveMass t-Real.log (2*A^(19 : ℝ)) := by
  rw [workingNoConnectorRate,Real.log_div (Real.exp_ne_zero _) (by positivity),Real.log_exp]
  ring

end
end StrongSilver
