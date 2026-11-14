-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.OrderedPowerFromReserve
import StrongSilver.SublistRankBudget

namespace StrongSilver
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2200000

/-- A compressed schedule pays its entire weighted selected-count error
to the rank budget of the original schedule. -/
theorem compressed_power_from_reserve {μ A B P cap E δ H : ℝ} (hμ : 0 < μ) (hA : 0 < A)
    (hAB : A < B) (hBcap : B ≤ cap) (hcap : μ*B ≤ 1/2) (hP : 0 < P)
    (hφA : P < cappedStep μ B A) (hE : 0 ≤ E) (hδ : 0 ≤ δ)
    (G h : List ℝ) (hsub : G.Sublist h)
    (hreserve : H ≤ cutPower (cappedStep μ B) P 0 (closedCut B G)-P^nu-
      splitCoefficient*(cappedStep μ B B-P)^nu*(cutLogProduct (cappedStep μ B) P 0 (closedCut B G)-Real.log P))
    (hL : let ps := orderedPositions G (eligibleIndices G Finset.univ A B)
      ∀ i ≤ ps.length, -E-δ*((countAbove G B : ℝ)+(i : ℝ)) ≤
        cutLogProduct (cappedStep μ B) P 0 (positionCut (fun _ b => decide (B ≤ b)) G (ps.take i))-Real.log P) :
    H-splitCoefficient*(2*E*B^nu+4*δ*weightedCount h cap*(1+Real.log (B/A))) ≤
      cutPower (cappedStep μ B) P 0 (fullCut A G)-P^nu := by
  have hφ := cappedStep_monotone hμ (by linarith only [hcap] : μ*B < 1)
  have hh := ordered_cut_power_from_reserve hφ G hAB hP hφA (by norm_num : (0 : ℝ) ≤ 0) hreserve hL
  have hw := selected_weighted_count_budget hμ hA hAB.le hBcap hcap hP.le hφA G Finset.univ
  have hlog := Real.log_nonneg ((one_le_div hA).mpr hAB.le)
  have hsubw := weightedCount_sublist_le hsub cap
  have hws := mul_le_mul_of_nonneg_left hsubw (show 0 ≤ 4*(1+Real.log (B/A)) by positivity)
  have hcount : (countAbove G B : ℝ)*(cappedStep μ B B-P)^nu+
      (∑ i ∈ Finset.range (orderedPositions G (eligibleIndices G Finset.univ A B)).length,
        eligibleRefinementWeights (cappedStep μ B) P G Finset.univ A B (i+1)) ≤
      4*weightedCount h cap*(1+Real.log (B/A)) := by linear_combination hw+hws
  have ht : 0 ≤ cappedStep μ B B-P := by have ht := hφ hAB.le; linarith only [ht,hφA]
  have hp := capped_pivot_power_le_two hμ hcap (hA.trans hAB) le_rfl hP.le ht
  have he := mul_le_mul_of_nonneg_left hp hE
  have hc := mul_le_mul_of_nonneg_left hcount hδ
  have hcost := mul_le_mul_of_nonneg_left (add_le_add he hc) split_coefficient_positive.le
  linear_combination hh+hcost

end
end StrongSilver
