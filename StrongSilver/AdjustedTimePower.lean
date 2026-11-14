-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BalancedSplitMasses

namespace StrongSilver.PaddedSplitInput
open Scalar.SignedIntervals
noncomputable section
set_option maxHeartbeats 3600000

def adjustedTime (S : PaddedSplitInput) : ℝ := S.t-drawdown S.left

def adjustedGain (S : PaddedSplitInput) : ℝ := splitGain S.a S.b S.adjustedTime S.z

theorem balanced_adjusted_weight {S : PaddedSplitInput} {δ : ℝ} (hδ : 0 ≤ δ) (hδmax : δ ≤ 1/4)
    (h : S.Balanced δ) : (1-δ)*S.weight ≤ S.adjustedTime^nu ∧ S.adjustedTime^nu ≤ S.weight := by
  have hid := balanced_drawdown_identity hδmax h
  have ht := S.t_positive
  have hd := drawdown_nonneg S.left
  have hT : 0 < S.adjustedTime := (by linarith only [ht] : 0 < 3*S.t/4).trans_le hid.2
  have hTt : S.adjustedTime ≤ S.t := sub_le_self _ hd
  have hRatio : 0 < S.adjustedTime/S.t := div_pos hT ht
  have hRatio1 : S.adjustedTime/S.t ≤ 1 := (div_le_one ht).mpr hTt
  have hPower := Real.rpow_le_rpow_of_exponent_ge hRatio hRatio1 nu_lt_one.le
  rw [Real.rpow_one,Real.div_rpow hT.le ht.le] at hPower
  have hW := S.weight_positive
  have hRatioW : S.adjustedTime/S.t*S.weight ≤ S.adjustedTime^nu := by
    apply (le_div_iff₀ hW).mp
    exact hPower
  have hBound : 1-δ ≤ S.adjustedTime/S.t := by
    apply (le_div_iff₀ ht).mpr
    have hh := (div_le_iff₀ ht).mp h.2.2
    dsimp only [adjustedTime]
    linarith only [hh]
  refine ⟨(mul_le_mul_of_nonneg_right hBound hW.le).trans hRatioW,?_⟩
  exact Real.rpow_le_rpow hT.le hTt nu_positive.le

/-- The first scalar step of (4.17): remove left drawdown from the
selected time before changing the offset from P to one. -/
theorem balanced_adjusted_power_decrease {S : PaddedSplitInput} {δ : ℝ} (hδ : 0 ≤ δ) (hδmax : δ ≤ 1/4)
    (h : S.Balanced δ) :
    S.decrease ≤ splitCoefficient*S.weight*S.adjustedGain+splitCoefficient*δ*S.weight*|S.adjustedGain| := by
  have hid := balanced_drawdown_identity hδmax h
  have ht := S.t_positive
  have hT : 0 < S.adjustedTime := (by linarith only [ht] : 0 < 3*S.t/4).trans_le hid.2
  have hz : S.z ≤ S.a+S.b+S.adjustedTime := by dsimp only [adjustedTime]; linarith only [hid.1]
  have hmain := split_power_decrease_le S.a S.b S.adjustedTime S.z S.valid.1 S.valid.2.1 hT S.valid.2.2.2.1 hz
  have hw := balanced_adjusted_weight hδ hδmax h
  have hAbs : |S.adjustedTime^nu-S.weight| ≤ δ*S.weight := by
    rw [abs_of_nonpos (sub_nonpos.mpr hw.2)]
    linarith only [hw.1]
  have hprod : (S.adjustedTime^nu-S.weight)*S.adjustedGain ≤ (δ*S.weight)*|S.adjustedGain| := le_trans (le_abs_self ((S.adjustedTime^nu-S.weight)*S.adjustedGain))
    (by rw [abs_mul]; exact mul_le_mul_of_nonneg_right hAbs (abs_nonneg S.adjustedGain))
  have hh := mul_le_mul_of_nonneg_left hprod split_coefficient_positive.le
  change S.decrease ≤ splitCoefficient*S.adjustedTime^nu*S.adjustedGain at hmain
  linear_combination hmain+hh

end
end StrongSilver.PaddedSplitInput
