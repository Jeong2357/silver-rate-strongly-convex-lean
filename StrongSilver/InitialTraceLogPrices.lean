-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.InitialReservedTrace
import StrongSilver.TraceLogPrices

namespace StrongSilver
open Real
noncomputable section
set_option maxHeartbeats 2000000

theorem initialBlockFactor_positive {κ B : ℝ} (hκ : 0 < κ) (hB : 0 < B) (μ : ℝ) (I : List ℝ) :
    0 < initialBlockFactor κ B μ I := by
  have hK := div_pos hκ hB
  have hs := div_nonneg (smallPositiveSum_nonneg μ I) hκ.le
  have hC := initialBlockConstant_positive
  unfold initialBlockFactor
  positivity

theorem log_initialBlockFactor {κ B : ℝ} (hκ : 0 < κ) (hB : 0 < B) (μ : ℝ) (I : List ℝ) :
    Real.log (initialBlockFactor κ B μ I) = Real.log initialBlockConstant+6*Real.log (κ/B)+
      inverseCharge μ I+Real.log (1+smallPositiveSum μ I/κ) := by
  have hK := div_pos hκ hB
  have hs : 0 < 1+smallPositiveSum μ I/κ := by have hh := div_nonneg (smallPositiveSum_nonneg μ I) hκ.le; linarith only [hh]
  have hC := initialBlockConstant_positive
  rw [initialBlockFactor,Real.log_mul (by positivity) hs.ne',
    Real.log_mul (by positivity) (Real.exp_ne_zero _),Real.log_mul hC.ne' (by positivity),Real.log_pow,Real.log_exp]
  norm_num

theorem initialReservedRate_positive {κ B r : ℝ} (hκ : 0 < κ) (hB : 0 < B) (hr : 0 < r) (μ : ℝ) (I : List ℝ) :
    0 < initialReservedRate κ B μ I r := by
  have hK := div_pos hκ hB
  have hC := initialEntryConstant_positive
  exact div_pos (div_pos hr (by positivity)) (sq_pos_of_pos (initialBlockFactor_positive hκ hB μ I))

theorem log_initialReservedRate {κ B r : ℝ} (hκ : 0 < κ) (hB : 0 < B) (hr : 0 < r) (μ : ℝ) (I : List ℝ) :
    Real.log (initialReservedRate κ B μ I r) = Real.log r-
      (Real.log initialEntryConstant+2*Real.log initialBlockConstant+16*Real.log (κ/B)+
        2*inverseCharge μ I+2*Real.log (1+smallPositiveSum μ I/κ)) := by
  have hK := div_pos hκ hB
  have hC := initialEntryConstant_positive
  rw [initialReservedRate,Real.log_div (by positivity) (pow_ne_zero 2 (initialBlockFactor_positive hκ hB μ I).ne'),
    Real.log_div hr.ne' (by positivity),Real.log_mul hC.ne' (by positivity),Real.log_pow,
    Real.log_pow,log_initialBlockFactor hκ hB]
  norm_num
  ring

theorem initialTerminalRate_positive {κ B : ℝ} (hκ : 0 < κ) (hB : 0 < B) (μ : ℝ) (I t : List ℝ) :
    0 < initialTerminalRate κ B μ I t := by
  have hK := div_pos hκ hB
  have hs := div_nonneg (smallPositiveSum_nonneg μ I) hκ.le
  have hC := initialEntryConstant_positive
  unfold initialTerminalRate
  positivity

theorem log_initialTerminalRate {κ B : ℝ} (hκ : 0 < κ) (hB : 0 < B) (μ : ℝ) (I t : List ℝ) :
    Real.log (initialTerminalRate κ B μ I t) = -4*(μ*Scalar.SignedIntervals.positiveMass t)-
      (Real.log (4*initialEntryConstant*(1200000 : ℝ)^2)+6*Real.log (κ/B)+
        2*inverseCharge μ I+2*Real.log (1+smallPositiveSum μ I/κ)) := by
  have hK := div_pos hκ hB
  have hs : 0 < 1+smallPositiveSum μ I/κ := by have hh := div_nonneg (smallPositiveSum_nonneg μ I) hκ.le; linarith only [hh]
  have hC := initialEntryConstant_positive
  rw [initialTerminalRate,Real.log_div (Real.exp_ne_zero _) (by positivity),Real.log_exp,
    Real.log_mul (by positivity) (by positivity),Real.log_mul (by positivity) (by positivity),
    Real.log_pow,Real.log_pow,Real.log_mul (Real.exp_ne_zero _) hs.ne',Real.log_exp]
  norm_num
  ring

theorem initialNoConnectorRate_positive {κ B : ℝ} (hκ : 0 < κ) (hB : 0 < B) (μ : ℝ) (I t : List ℝ) :
    0 < initialNoConnectorRate κ B μ I t := by
  have hK := div_pos hκ hB
  have hC := initialEntryConstant_positive
  unfold initialNoConnectorRate
  positivity

theorem log_initialNoConnectorRate {κ B : ℝ} (hκ : 0 < κ) (hB : 0 < B) (μ : ℝ) (I t : List ℝ) :
    Real.log (initialNoConnectorRate κ B μ I t) =
      -2*inverseCharge μ I-4*μ*Scalar.SignedIntervals.positiveMass t-Real.log (2*initialEntryConstant)-4*Real.log (κ/B) := by
  have hK := div_pos hκ hB
  have hC := initialEntryConstant_positive
  rw [initialNoConnectorRate,Real.log_div (Real.exp_ne_zero _) (by positivity),Real.log_exp,
    Real.log_mul (by positivity) (by positivity),Real.log_pow]
  norm_num
  ring

end
end StrongSilver
