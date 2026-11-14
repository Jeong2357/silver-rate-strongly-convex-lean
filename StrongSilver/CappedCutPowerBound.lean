-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ShiftedCutPowerBound
import StrongSilver.CappedPivotMoments

namespace StrongSilver
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2200000

theorem half_scale_power_lower {B t : ℝ} (hB : 0 < B) (ht : B/2 ≤ t) : B^nu/2 ≤ t^nu := by
  have hhalf : 0 < B/2 := div_pos hB (by norm_num)
  have hp := Real.rpow_le_rpow hhalf.le ht nu_positive.le
  have htwo : (2 : ℝ)^nu ≤ 2 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) nu_lt_one.le
  have he : B^nu = (2 : ℝ)^nu*(B/2)^nu := by
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hhalf.le]
    congr 1
    ring
  have hh := mul_le_mul_of_nonneg_right htwo (Real.rpow_pos_of_pos hhalf nu).le
  nlinarith only [hp,hh,he]

/-- Finite full-cut form of the reserve argument. The logarithmic budget is
an explicit input here; all insertions, weights and rank-moment charges are
constructed from the schedule. -/
theorem capped_full_cut_power_lower {κ μ A B P cap E δ : ℝ} (hμ : 0 < μ) (hA : 0 < A)
    (hAB : A < B) (hBcap : B ≤ cap) (hcap : μ*B ≤ 1/2) (hP : 0 < P) (hPB : P ≤ B/2)
    (hφA : P < cappedStep μ B A) (hκ : 0 < κ) (hBκ : 2*B ≤ κ) (hE : 0 ≤ E) (hδ : 0 ≤ δ)
    (h : List ℝ) (hmax : weightedCount h cap = (countAbove h B : ℝ)*B^nu)
    (hL : let ps := orderedPositions h (eligibleIndices h Finset.univ A B)
      ∀ i ≤ ps.length, -E-δ*((countAbove h B : ℝ)+(i : ℝ)) ≤
        cutLogProduct (cappedStep μ B) P κ (positionCut (fun _ b => decide (B ≤ b)) h (ps.take i))-Real.log κ) :
    (powerLogMinimum/2)*weightedCount h cap-
      splitCoefficient*(2*E*B^nu+4*δ*weightedCount h cap*(1+Real.log (B/A))) ≤
      cutPower (cappedStep μ B) P κ (fullCut A h) := by
  have hB := hA.trans hAB
  have hφ := cappedStep_monotone hμ (by linarith only [hcap] : μ*B < 1)
  have hb : 0 ≤ cappedStep μ B B-P := by have hh := hφ hAB.le; linarith only [hh,hφA]
  have hpow := capped_pivot_power_le_two hμ hcap hB le_rfl hP.le hb
  have htwoB : cappedStep μ B B ≤ 2*B := by
    have hd := (cappedStep_defect (b := B) hμ hcap).2
    rw [min_self] at hd
    have hm := mul_le_mul_of_nonneg_right hcap hB.le
    nlinarith only [hd,hm]
  have hbr : cappedStep μ B B-P ≤ κ := by linarith only [htwoB,hBκ,hP]
  have hlower := ordered_full_cut_power_lower hφ h hAB hP hφA hκ hbr hL
  have hcount := selected_weighted_count_budget hμ hA hAB.le hBcap hcap hP.le hφA h Finset.univ
  have hcost : E*(cappedStep μ B B-P)^nu+δ*((countAbove h B : ℝ)*(cappedStep μ B B-P)^nu+
      ∑ i ∈ Finset.range (orderedPositions h (eligibleIndices h Finset.univ A B)).length,
        eligibleRefinementWeights (cappedStep μ B) P h Finset.univ A B (i+1)) ≤
      2*E*B^nu+4*δ*weightedCount h cap*(1+Real.log (B/A)) := by
    have he := mul_le_mul_of_nonneg_left hpow hE
    have hc := mul_le_mul_of_nonneg_left hcount hδ
    nlinarith only [he,hc]
  have hbase : B/2 ≤ cappedStep μ B B-P := by
    have hh := cappedStep_ge hμ (by linarith only [hcap] : μ*B < 1) B
    linarith only [hh,hPB]
  have hpowlower := half_scale_power_lower hB hbase
  have hreserve : (powerLogMinimum/2)*weightedCount h cap ≤
      ((countAbove h B : ℝ)+1)*powerLogMinimum*(cappedStep μ B B-P)^nu := by
    rw [hmax]
    have hc0 : (0 : ℝ) ≤ (countAbove h B : ℝ) := Nat.cast_nonneg _
    have hh := mul_le_mul_of_nonneg_left hpowlower (mul_nonneg hc0 powerLogMinimum_positive.le)
    have hpos := mul_nonneg powerLogMinimum_positive.le (Real.rpow_nonneg (by linarith only [hbase,hB] : 0 ≤ cappedStep μ B B-P) nu)
    nlinarith only [hh,hpos]
  have hcost' := mul_le_mul_of_nonneg_left hcost split_coefficient_positive.le
  nlinarith only [hlower,hreserve,hcost']

end
end StrongSilver
