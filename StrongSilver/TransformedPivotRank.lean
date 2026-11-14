-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.HeightStripRank
import StrongSilver.LinkedFollowingSum

namespace StrongSilver
open ScheduleTree BinaryForest Real
noncomputable section
set_option maxHeartbeats 5800000

theorem word_threshold_indicator_sum (h : List ℝ) (A : ℝ) :
    (h.map fun b => if A ≤ b then (1:ℝ) else 0).sum = (countAbove h A:ℝ) := by
  induction h with
  | nil => simp
  | cons b h ih =>
    rw [List.map_cons,List.sum_cons,ih,countAbove_cons,Nat.cast_add]
    split_ifs <;> norm_num

/-- Rank control for all transformed original pivots above a height,
including pivots above the transform cap. -/
theorem transformed_pivot_rank {κ μ B P z cap : ℝ} (hμ : 0 < μ) (hB : 0 < B)
    (hμB : μ*B ≤ 1/2) (hP : 0 ≤ P) (hA : Real.exp z/2 ≤ cap) (h : List ℝ) :
    Real.exp (nu*z)*((labels ((cartesian h).indexedTree 0 κ)).map fun q =>
      if P+Real.exp z < cappedStep μ B q.pivot then (1:ℝ) else 0).sum ≤ 2*weightedCount h cap := by
  let A := Real.exp z/2
  let f := fun b => if P+Real.exp z < cappedStep μ B b then (1:ℝ) else 0
  have hA0 : 0 < A := by dsimp only [A]; positivity
  have hf : ∀ b, 0 ≤ f b := by intro b; dsimp only [f]; split_ifs <;> norm_num
  have hNodes := indexedTree_pivot_weight_le_word f hf 0 κ (cartesian h)
  rw [cartesian_word] at hNodes
  have hWord : (h.map f).sum ≤ (countAbove h A:ℝ) := by
    rw [← word_threshold_indicator_sum]
    apply List.sum_le_sum
    intro b hb
    dsimp only [f]
    by_cases hs : P+Real.exp z < cappedStep μ B b
    · have hUpper := (le_max_left (cappedStep μ B b) 0).trans (cappedStep_positive_upper_global hμ hB hμB b)
      have hb0 : 0 < b := by
        by_contra hh
        have hz : max b 0 = 0 := max_eq_right (le_of_not_gt hh)
        rw [hz,mul_zero] at hUpper
        have hp := Real.exp_pos z
        linarith only [hUpper,hs,hP,hp]
      rw [max_eq_left hb0.le] at hUpper
      have hAb : A ≤ b := by dsimp only [A]; linarith only [hUpper,hs,hP]
      simp only [if_pos hs,if_pos hAb,le_refl]
    · rw [if_neg hs]
      split_ifs <;> norm_num
  have hCount := hNodes.trans hWord
  have hRank := threshold_le_weightedCount h hA0 hA
  have hTwo : (2:ℝ)^nu ≤ 2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) nu_lt_one.le
  have hExp : Real.exp (nu*z) ≤ 2*A^nu := by
    have hEq : Real.exp (nu*z) = (2:ℝ)^nu*A^nu := by
      rw [← Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hA0.le]
      have he : (2:ℝ)*A = Real.exp z := by dsimp only [A]; ring
      rw [he,Real.rpow_def_of_pos (Real.exp_pos z),Real.log_exp,mul_comm]
    rw [hEq]
    exact mul_le_mul_of_nonneg_right hTwo (Real.rpow_pos_of_pos hA0 nu).le
  have h1 := mul_le_mul_of_nonneg_left hCount (Real.exp_pos (nu*z)).le
  have h2 := mul_le_mul_of_nonneg_right hExp (Nat.cast_nonneg (countAbove h A) : (0:ℝ) ≤ countAbove h A)
  change _ ≤ _ at h1
  linear_combination h1+h2+2*hRank

end
end StrongSilver
