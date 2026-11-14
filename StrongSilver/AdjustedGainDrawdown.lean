-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.UnitOffsetGainComparison

namespace StrongSilver.PaddedSplitInput
open Scalar.SignedIntervals
noncomputable section
set_option maxHeartbeats 3200000

/-- The logarithmic correction for removing left drawdown from the
selected factor is controlled by its relative drawdown. -/
theorem adjusted_gain_drawdown_error {S : PaddedSplitInput} {δ : ℝ} (hδmax : δ ≤ 1/4)
    (h : S.Balanced δ) : |S.adjustedGain-S.gain| ≤ 2*drawdown S.left/S.t := by
  have ht := S.t_positive
  have hs : 0 < S.t/2 := by positivity
  have hid := balanced_drawdown_identity hδmax h
  have hT : S.t/2 ≤ S.adjustedTime := by dsimp only [adjustedTime]; linarith only [hid.2,ht]
  have htT : S.t/2 ≤ S.t := by linarith only [ht]
  have hd := drawdown_nonneg S.left
  have hdiff : |S.adjustedTime-S.t| ≤ drawdown S.left := by
    dsimp only [adjustedTime]
    rw [sub_sub_cancel_left,abs_neg,abs_of_nonneg hd]
  have hh := log_mass_perturbation hs hT htT hd hdiff
  have hEq : S.adjustedGain-S.gain = Real.log S.adjustedTime-Real.log S.t := by
    unfold adjustedGain gain splitGain
    rw [Real.log_div (mul_pos (hs.trans_le hT) (S.valid.1.trans_le S.valid.2.2.2.1)).ne' (mul_pos S.valid.1 S.valid.2.1).ne',
      Real.log_div (mul_pos ht (S.valid.1.trans_le S.valid.2.2.2.1)).ne' (mul_pos S.valid.1 S.valid.2.1).ne',
      Real.log_mul (hs.trans_le hT).ne' (S.valid.1.trans_le S.valid.2.2.2.1).ne',
      Real.log_mul ht.ne' (S.valid.1.trans_le S.valid.2.2.2.1).ne']
    ring
  rw [hEq]
  have hdiv : drawdown S.left/(S.t/2) = 2*drawdown S.left/S.t := by field_simp
  exact hh.trans_eq hdiv

/-- The precise offset-one logarithm used by the local trajectory
construction differs from the cut logarithm by drawdown and pad errors. -/
theorem unit_offset_original_gain_error {S : PaddedSplitInput} {δ : ℝ}
    (hP : 1 ≤ S.pad) (hsmall : S.pad ≤ S.t/4) (hres : S.reserve = 0)
    (hδ : 0 ≤ δ) (hδmax : δ ≤ 1/4) (h : S.Balanced δ) :
    |S.unitOffsetGain-S.gain| ≤ 2*drawdown S.left/S.t+8*S.pad/S.t := by
  have h1 := unit_offset_gain_comparison hP hsmall hres hδ hδmax h
  have h2 := adjusted_gain_drawdown_error hδmax h
  exact (abs_sub_le S.unitOffsetGain S.adjustedGain S.gain).trans (by linarith only [h1,h2])

end
end StrongSilver.PaddedSplitInput
