-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.IndexWeightSums
import StrongSilver.PowerReservePropagation
import StrongSilver.CappedTransform
import Mathlib.Algebra.BigOperators.Ring.List

namespace StrongSilver
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2200000

theorem capped_pivot_power_le_two {μ B P b : ℝ} (hμ : 0 < μ) (hcap : μ*B ≤ 1/2) (hb : 0 < b)
    (hbB : b ≤ B) (hP : 0 ≤ P) (ht : 0 ≤ cappedStep μ B b-P) :
    (cappedStep μ B b-P)^nu ≤ 2*b^nu := by
  have hd := (cappedStep_defect (b := b) hμ hcap).2
  rw [min_eq_left hbB] at hd
  have hμb := (mul_le_mul_of_nonneg_left hbB hμ.le).trans hcap
  have hmul := mul_le_mul_of_nonneg_right hμb hb.le
  have hφ : cappedStep μ B b ≤ 2*b := by nlinarith only [hd,hmul]
  have hp := Real.rpow_le_rpow ht (by linarith only [hφ,hP] : cappedStep μ B b-P ≤ 2*b) nu_positive.le
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hb.le] at hp
  have htwo : (2 : ℝ)^nu ≤ 2 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) nu_lt_one.le
    simpa only [Real.rpow_one] using hh
  exact hp.trans (mul_le_mul_of_nonneg_right htwo (Real.rpow_pos_of_pos hb nu).le)

theorem eligible_capped_weight_sum_bound {μ A B P cap : ℝ} (hμ : 0 < μ) (hA : 0 < A)
    (hAB : A ≤ B) (hcapB : B ≤ cap) (hcap : μ*B ≤ 1/2) (hP : 0 ≤ P) (hφA : P < cappedStep μ B A)
    (h : List ℝ) (R : Finset (Fin h.length)) :
    (eligiblePivotWeights (cappedStep μ B) P h R A B).sum ≤ 2*weightedCount h cap*(1+Real.log (B/A)) := by
  have hcap1 : μ*B < 1 := by linarith only [hcap]
  have hφ := cappedStep_monotone hμ hcap1
  have hh : (eligiblePivotWeights (cappedStep μ B) P h R A B).sum ≤
      ((orderedPositions h (eligibleIndices h R A B)).map fun p => 2*(stepAt h p)^nu).sum := by
    apply List.sum_le_sum
    intro p hp
    obtain ⟨hpA,hpB⟩ := eligible_positions_range h R A B p hp
    have ht : 0 ≤ cappedStep μ B (stepAt h p)-P := by
      have hmono := hφ hpA.le
      linarith only [hmono,hφA]
    exact capped_pivot_power_le_two hμ hcap (hA.trans hpA) hpB.le hP ht
  rw [List.sum_map_mul_left] at hh
  have hm := mul_le_mul_of_nonneg_left (eligible_power_sum_rank_bound hA hAB hcapB h R) (by norm_num : (0 : ℝ) ≤ 2)
  exact hh.trans (hm.trans_eq (by ring))

theorem eligible_capped_refinement_sum_bound {μ A B P cap : ℝ} (hμ : 0 < μ) (hA : 0 < A)
    (hAB : A ≤ B) (hcapB : B ≤ cap) (hcap : μ*B ≤ 1/2) (hP : 0 ≤ P) (hφA : P < cappedStep μ B A)
    (h : List ℝ) (R : Finset (Fin h.length)) :
    (∑ i ∈ Finset.range (orderedPositions h (eligibleIndices h R A B)).length,
      eligibleRefinementWeights (cappedStep μ B) P h R A B (i+1)) ≤ 2*weightedCount h cap*(1+Real.log (B/A)) := by
  have he := sum_refinementWeights ((cappedStep μ B B-P)^nu) (eligiblePivotWeights (cappedStep μ B) P h R A B)
  have he' : (∑ i ∈ Finset.range (orderedPositions h (eligibleIndices h R A B)).length,
      eligibleRefinementWeights (cappedStep μ B) P h R A B (i+1)) = (eligiblePivotWeights (cappedStep μ B) P h R A B).sum := by
    simpa only [eligibleRefinementWeights,eligiblePivotWeights,List.length_map] using he
  exact he'.trans_le (eligible_capped_weight_sum_bound hμ hA hAB hcapB hcap hP hφA h R)

theorem initial_selected_weight_bound {μ A B P cap : ℝ} (hμ : 0 < μ) (hA : 0 < A)
    (hAB : A ≤ B) (hcapB : B ≤ cap) (hcap : μ*B ≤ 1/2) (hP : 0 ≤ P) (hφA : P < cappedStep μ B A) (h : List ℝ) :
    (countAbove h B : ℝ)*(cappedStep μ B B-P)^nu ≤ 2*weightedCount h cap := by
  have hB := hA.trans_le hAB
  have hφ := cappedStep_monotone hμ (by linarith only [hcap] : μ*B < 1)
  have ht : 0 ≤ cappedStep μ B B-P := by have hh := hφ hAB; linarith only [hh,hφA]
  have hp := capped_pivot_power_le_two hμ hcap hB le_rfl hP ht
  have hcount := threshold_le_weightedCount h hB hcapB
  have hm := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg (countAbove h B) : (0 : ℝ) ≤ (countAbove h B : ℝ))
  nlinarith only [hm,hcount]

theorem selected_weighted_count_budget {μ A B P cap : ℝ} (hμ : 0 < μ) (hA : 0 < A)
    (hAB : A ≤ B) (hcapB : B ≤ cap) (hcap : μ*B ≤ 1/2) (hP : 0 ≤ P) (hφA : P < cappedStep μ B A)
    (h : List ℝ) (R : Finset (Fin h.length)) :
    (countAbove h B : ℝ)*(cappedStep μ B B-P)^nu+
      (∑ i ∈ Finset.range (orderedPositions h (eligibleIndices h R A B)).length,
        eligibleRefinementWeights (cappedStep μ B) P h R A B (i+1)) ≤
      4*weightedCount h cap*(1+Real.log (B/A)) := by
  have hi := initial_selected_weight_bound hμ hA hAB hcapB hcap hP hφA h
  have hs := eligible_capped_refinement_sum_bound hμ hA hAB hcapB hcap hP hφA h R
  have hlog := Real.log_nonneg ((one_le_div hA).mpr hAB)
  have hp := mul_nonneg (weightedCount_nonneg h cap) hlog
  nlinarith only [hi,hs,hp]

end
end StrongSilver
