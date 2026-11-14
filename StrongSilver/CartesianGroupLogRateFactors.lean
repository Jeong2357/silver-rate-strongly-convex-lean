-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CartesianGroupLogRate

namespace StrongSilver.ScheduleTree.FourGapGroup
open FourPhase
noncomputable section
set_option maxHeartbeats 2400000

theorem sequenceRate_positive_of_factors {C μ B ε η Z : ℝ} {qs : List Group}
    (h : ∀ q ∈ qs, 0 < q.1.leadingFactor μ B q.2) : 0 < sequenceRate C μ B ε η qs Z := by
  induction qs with
  | nil => exact zero_lt_one
  | cons q qs ih =>
    exact mul_pos (ih (fun p hp => h p (List.mem_cons_of_mem q hp)))
      (mul_pos (Real.exp_pos _) (sq_pos_of_pos (h q (by simp))))

theorem log_sequenceRate_of_factors {C μ B ε η Z : ℝ} {qs : List Group}
    (h : ∀ q ∈ qs, 0 < q.1.leadingFactor μ B q.2) :
    Real.log (sequenceRate C μ B ε η qs Z) =
      (qs.map fun q => signedThreeGain (rootGain (logarithmicStep μ) q.1.tree)
        (rootGain (logarithmicStep μ) q.1.left) (rootGain (logarithmicStep μ) q.1.right)).sum+
      2*(qs.map fun q => Real.log (q.1.leadingFactor μ B q.2)).sum-C*sequenceLoss μ ε η qs Z := by
  induction qs with
  | nil => simp [sequenceRate,sequenceLoss]
  | cons q qs ih =>
    have htail := fun p hp => h p (List.mem_cons_of_mem q hp)
    have ht := sequenceRate_positive_of_factors (C := C) (ε := ε) (η := η) (Z := Z) htail
    have hp := h q (by simp)
    rw [sequenceRate,Real.log_mul ht.ne' (mul_pos (Real.exp_pos _) (sq_pos_of_pos hp)).ne',
      Real.log_mul (Real.exp_ne_zero _) (sq_pos_of_pos hp).ne',Real.log_exp,Real.log_pow,ih htail]
    simp only [List.map_cons,List.sum_cons,sequenceLoss,gainLower,groupLoss]
    ring

end
end StrongSilver.ScheduleTree.FourGapGroup
