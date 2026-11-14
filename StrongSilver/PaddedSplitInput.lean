-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PaddedGapSplit

namespace StrongSilver
open Scalar.SignedIntervals
noncomputable section
set_option maxHeartbeats 2400000

/-- Actual signed transformed words around one original pivot. The
terminal reserve is passed only to the right child. -/
structure PaddedSplitInput where
  left : List ℝ
  right : List ℝ
  pivot : ℝ
  pad : ℝ
  reserve : ℝ
  pad_positive : 0 < pad
  reserve_nonnegative : 0 ≤ reserve
  pivot_large : pad < pivot

namespace PaddedSplitInput

def a (S : PaddedSplitInput) : ℝ := prefixMax S.left+S.pad
def b (S : PaddedSplitInput) : ℝ := prefixMax S.right+S.pad+S.reserve
def t (S : PaddedSplitInput) : ℝ := S.pivot-S.pad
def z (S : PaddedSplitInput) : ℝ := prefixMax (S.left++S.pivot::S.right)+S.pad+S.reserve
def weight (S : PaddedSplitInput) : ℝ := S.t^nu
def gain (S : PaddedSplitInput) : ℝ := splitGain S.a S.b S.t S.z
def excess (S : PaddedSplitInput) : ℝ := splitExcess S.a S.b S.t S.z
def decrease (S : PaddedSplitInput) : ℝ := powerDecrease S.a S.b S.z

def Balanced (S : PaddedSplitInput) (δ : ℝ) : Prop :=
  |Real.log (S.a/(rho*S.t))| ≤ δ ∧ |Real.log (S.b/(rho*S.t))| ≤ δ ∧ drawdown S.left/S.t ≤ δ

theorem valid (S : PaddedSplitInput) : 0 < S.a ∧ 0 < S.b ∧ 0 < S.t ∧ S.a ≤ S.z ∧ S.z ≤ S.a+S.b+S.t ∧
    S.a+S.b+S.t-S.z = min (drawdown S.left) (S.pivot+prefixMax S.right) :=
  padded_gap_split_masses S.left S.right S.pad_positive S.reserve_nonnegative S.pivot_large

theorem t_positive (S : PaddedSplitInput) : 0 < S.t := S.valid.2.2.1

theorem weight_positive (S : PaddedSplitInput) : 0 < S.weight := Real.rpow_pos_of_pos S.t_positive _

theorem excess_nonnegative (S : PaddedSplitInput) : 0 ≤ S.excess :=
  split_excess_nonnegative S.a S.b S.t S.z S.valid.1 S.valid.2.1 S.t_positive S.valid.2.2.2.1 S.valid.2.2.2.2.1

theorem decrease_identity (S : PaddedSplitInput) : S.decrease = splitCoefficient*S.weight*S.gain-S.excess := by
  unfold decrease excess gain weight splitExcess
  ring

theorem deficit_nonnegative (S : PaddedSplitInput) : 0 ≤ (S.a+S.b+S.t-S.z)/S.t :=
  div_nonneg (by linarith only [S.valid.2.2.2.2.1]) S.t_positive.le

theorem pivot_right_ge_time (S : PaddedSplitInput) : S.t ≤ S.pivot+prefixMax S.right := by
  have hp := prefixMax_nonneg S.right
  unfold t
  linarith only [hp,S.pad_positive]

end PaddedSplitInput
end
end StrongSilver
