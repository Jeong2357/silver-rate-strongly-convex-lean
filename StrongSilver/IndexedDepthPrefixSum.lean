-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.DepthPrefixPartition
import StrongSilver.CartesianGainAggregation

namespace StrongSilver
open ScheduleTree BinaryForest
noncomputable section
set_option maxHeartbeats 4200000

theorem indexed_depth_prefix_sum (f : ScheduleTree → ℝ) (k start : ℕ) (κ : ℝ) (t : ScheduleTree) :
    ((depthPrefixLabels k (t.indexedTree start κ)).map fun q => f q.source).sum = throughSum f k t := by
  induction k generalizing start κ t with
  | zero => rfl
  | succ k ih =>
    cases t with
    | leaf word => rfl
    | split l b r => simp only [indexedTree,depthPrefixLabels,List.map_cons,List.map_append,List.sum_cons,List.sum_append,ih,throughSum] <;> ring

theorem depthPrefixLabels_length_bound {α : Type*} (k : ℕ) (t : BinaryTree α) : (depthPrefixLabels k t).length+1 ≤ 2^k := by
  induction k generalizing t with
  | zero => simp [depthPrefixLabels]
  | succ k ih =>
    cases t with
    | nil => simpa only [depthPrefixLabels,List.length_nil,zero_add] using Nat.one_le_pow k.succ 2 (by decide)
    | node v l r =>
      have hl := ih l
      have hr := ih r
      simp only [depthPrefixLabels,List.length_cons,List.length_append,pow_succ]
      omega

end
end StrongSilver
