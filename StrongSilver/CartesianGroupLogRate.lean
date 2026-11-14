-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CartesianGroupAssembly

namespace StrongSilver.ScheduleTree.FourGapGroup
open FourPhase Scalar.SignedIntervals
noncomputable section
set_option maxHeartbeats 3000000

def groupLoss (G : FourGapGroup) (μ T b ε η Z : ℝ) : ℝ :=
  (ε+μ*T)*(|rootGain (logarithmicStep μ) G.tree|+|rootGain (logarithmicStep μ) G.left|+
    |rootGain (logarithmicStep μ) G.right|)+μ*T+μ*b+η+
    lastExcess μ T G.gaps (G.pivots b)*Z

def sequenceLoss (μ ε η : ℝ) : List Group → ℝ → ℝ
  | [],_ => 0
  | q::qs,Z => groupLoss q.1 μ (groupScale μ q) q.2 ε η (firstOffset qs Z)+sequenceLoss μ ε η qs Z

theorem leadingFactor_positive {G : FourGapGroup} {μ T b ε B : ℝ}
    (D : BalancedGroupData G μ T b ε) (hμB : μ*B ≤ 1/2) : 0 < G.leadingFactor μ B b :=
  div_pos (D.exterior_excess_positive hμB) (prefixMass_positive (logarithmicStep μ) G.tree)

theorem sequenceRate_positive {δ c μ ε B H Z C η : ℝ} {qs : List Group}
    (hready : sequenceReady δ c μ ε qs H Z) (hμB : μ*B ≤ 1/2) :
    0 < sequenceRate C μ B ε η qs Z := by
  induction qs with
  | nil => exact zero_lt_one
  | cons q qs ih =>
    exact mul_pos (ih hready.2) (mul_pos (Real.exp_pos _) (sq_pos_of_pos (leadingFactor_positive hready.1.data hμB)))

/-- Exact logarithmic accounting of the constructed trajectory rate.
The three tree gains, every leading factor, the gate, and the single
rightmost height offset all remain in the finite identity. -/
theorem log_sequenceRate {δ c μ ε B H Z C η : ℝ} {qs : List Group}
    (hready : sequenceReady δ c μ ε qs H Z) (hμB : μ*B ≤ 1/2) :
    Real.log (sequenceRate C μ B ε η qs Z) =
      (qs.map fun q => signedThreeGain (rootGain (logarithmicStep μ) q.1.tree)
        (rootGain (logarithmicStep μ) q.1.left) (rootGain (logarithmicStep μ) q.1.right)).sum+
      2*(qs.map fun q => Real.log (q.1.leadingFactor μ B q.2)).sum-C*sequenceLoss μ ε η qs Z := by
  induction qs with
  | nil => simp [sequenceRate,sequenceLoss]
  | cons q qs ih =>
    have ht := sequenceRate_positive (C := C) (η := η) hready.2 hμB
    have hp := leadingFactor_positive hready.1.data hμB
    rw [sequenceRate,Real.log_mul ht.ne' (mul_pos (Real.exp_pos _) (sq_pos_of_pos hp)).ne',
      Real.log_mul (Real.exp_ne_zero _) (sq_pos_of_pos hp).ne',Real.log_exp,Real.log_pow,ih hready.2]
    simp only [List.map_cons,List.sum_cons,sequenceLoss,gainLower,groupLoss]
    ring

end
end StrongSilver.ScheduleTree.FourGapGroup
