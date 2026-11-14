-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.AdjustedGainDrawdown

namespace StrongSilver.PaddedSplitInput
noncomputable section
set_option maxHeartbeats 3200000

/-- The pointwise power estimate in (4.17), with explicit pad error
before replacing P/t by its uniform exponential band bound. -/
theorem unit_offset_power_decrease {S : PaddedSplitInput} {δ : ℝ}
    (hP : 1 ≤ S.pad) (hsmall : S.pad ≤ S.t/4) (hres : S.reserve = 0)
    (hδ : 0 ≤ δ) (hδmax : δ ≤ 1/4) (h : S.Balanced δ) :
    S.decrease ≤ splitCoefficient*S.weight*S.unitOffsetGain+
      splitCoefficient*δ*S.weight*|S.unitOffsetGain|+16*splitCoefficient*S.weight*(S.pad/S.t) := by
  have hc := split_coefficient_positive
  have hw := S.weight_positive
  have herror := unit_offset_gain_comparison hP hsmall hres hδ hδmax h
  have hmain := balanced_adjusted_power_decrease hδ hδmax h
  let e := 8*S.pad/S.t
  have he : 0 ≤ e := by dsimp only [e]; exact div_nonneg (mul_nonneg (by norm_num) S.pad_positive.le) S.t_positive.le
  have hGa : S.adjustedGain ≤ S.unitOffsetGain+e := by
    have hh := (abs_le.mp herror).1
    dsimp only [e]
    linarith only [hh]
  have hAbs : |S.adjustedGain| ≤ |S.unitOffsetGain|+e := by
    have hh := abs_sub_le S.adjustedGain S.unitOffsetGain (0:ℝ)
    rw [sub_zero,sub_zero,abs_sub_comm S.adjustedGain S.unitOffsetGain] at hh
    linarith only [hh,herror]
  have h1 := mul_le_mul_of_nonneg_left hGa (mul_pos hc hw).le
  have h2 := mul_le_mul_of_nonneg_left hAbs (mul_nonneg (mul_nonneg hc.le hδ) hw.le)
  have hδ1 : δ ≤ 1 := hδmax.trans (by norm_num)
  have h3 := mul_le_mul_of_nonneg_left hδ1 (mul_nonneg (mul_pos hc hw).le he)
  dsimp only [e] at h1 h2 h3
  linear_combination hmain+h1+h2+h3

end
end StrongSilver.PaddedSplitInput
