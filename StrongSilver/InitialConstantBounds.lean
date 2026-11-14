-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.InitialRaiseScale
import StrongSilver.InitialQueryBounds

namespace StrongSilver
open Real
noncomputable section
set_option maxHeartbeats 1000000

theorem initialPlaneConstant_ge_one : 1 ≤ initialPlaneConstant := by
  have hh : 1 ≤ Real.exp 4 := Real.one_le_exp_iff.mpr (by norm_num)
  unfold initialPlaneConstant
  linarith only [hh]

theorem initialScalarStartConstant_ge_one : 1 ≤ initialScalarStartConstant := by
  have hh : 1 ≤ Real.exp 2 := Real.one_le_exp_iff.mpr (by norm_num)
  unfold initialScalarStartConstant
  linarith only [hh]

theorem initialQueryConstant_ge_one : 1 ≤ initialQueryConstant := by
  have hC := initialPlaneConstant_ge_one
  have hh := mul_nonneg (Real.exp_pos 2).le initialQuadraticConstant_positive.le
  unfold initialQueryConstant
  linarith only [hC,hh]

theorem initialPointRelativeConstant_ge_one : 1 ≤ initialPointRelativeConstant := by
  have hq := initialQueryConstant_ge_one
  have hs := initialScalarStartConstant_ge_one
  have hh := mul_le_mul hq hs (by norm_num : (0 : ℝ) ≤ 1) initialQueryConstant_positive.le
  simpa only [one_mul,initialPointRelativeConstant] using hh

theorem initialSourceSlopeConstant_ge_one : 1 ≤ initialSourceSlopeConstant := by
  have hp := initialPlaneConstant_ge_one
  have hh := mul_nonneg initialPlaneConstant_positive.le initialScalarSlopeConstant_positive.le
  unfold initialSourceSlopeConstant
  linarith only [hp,hh]

theorem initialGateConstant_le_one : initialGateConstant ≤ 1 := by
  have hh := initialHeightConstant_ge_one
  have hs := initialSourceSlopeConstant_ge_one
  have hprod := mul_le_mul hh hs (by norm_num : (0 : ℝ) ≤ 1) initialHeightConstant_positive.le
  unfold initialGateConstant
  apply (div_le_one (by have := initialHeightConstant_positive; have := initialSourceSlopeConstant_positive; positivity)).mpr
  nlinarith only [hprod]

end
end StrongSilver
