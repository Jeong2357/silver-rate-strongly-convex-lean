-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.EligibleWeights
import StrongSilver.PowerMomentBudget
import Mathlib.Algebra.BigOperators.Fin

namespace StrongSilver
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1800000

theorem sum_schedule_values (f : ℝ → ℝ) (h : List ℝ) :
    (∑ p : Fin h.length, f h[p]) = (h.map f).sum := by
  have he := congrArg (List.map f) (List.ofFn_get h)
  rw [List.map_ofFn] at he
  have he' : List.ofFn (fun p : Fin h.length => f h[p]) = h.map f := by
    simpa only [Function.comp_def,List.get_eq_getElem,Fin.getElem_fin] using he
  rw [← List.sum_ofFn,he']

theorem sorted_indices_weight_sum (h : List ℝ) (E : Finset (Fin h.length)) (f : Fin h.length → ℝ) :
    ((sortedScheduleIndices h E).map f).sum = ∑ p ∈ E, f p := by
  have hh := List.sum_toFinset f (sortedScheduleIndices_nodup h E)
  have he : (sortedScheduleIndices h E).toFinset = E := Finset.sort_toFinset E _
  rw [he] at hh
  exact hh.symm

theorem ordered_positions_weight_sum (f : ℝ → ℝ) (h : List ℝ) (E : Finset (Fin h.length)) :
    ((orderedPositions h E).map fun p => f (stepAt h p)).sum = ∑ p ∈ E, f h[p] := by
  have he : (orderedPositions h E).map (fun p => f (stepAt h p)) = (sortedScheduleIndices h E).map (fun p => f h[p]) := by
    rw [orderedPositions,List.map_map]
    apply List.map_congr_left
    intro p _
    simp only [Function.comp_apply,stepAt_eq p.isLt,Fin.getElem_fin]
  rw [he,sorted_indices_weight_sum]

theorem cappedPowerAbove_nonnegative {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B) (b : ℝ) : 0 ≤ cappedPowerAbove A B b := by
  unfold cappedPowerAbove
  split_ifs with hb
  · exact (Real.rpow_pos_of_pos (hA.trans_le (le_min hb hAB)) nu).le
  · exact le_rfl

theorem eligible_power_sum_le_moment {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B)
    (h : List ℝ) (R : Finset (Fin h.length)) :
    ((orderedPositions h (eligibleIndices h R A B)).map fun p => (stepAt h p)^nu).sum ≤ powerMoment h A B := by
  rw [ordered_positions_weight_sum (fun x : ℝ => x^nu) h (eligibleIndices h R A B)]
  let E := eligibleIndices h R A B
  have he : (∑ p ∈ E, h[p]^nu) = ∑ p ∈ E, cappedPowerAbove A B h[p] := by
    apply Finset.sum_congr rfl
    intro p hp
    have hh := (Finset.mem_filter.mp hp).2
    simp only [cappedPowerAbove,if_pos hh.1.le,min_eq_left hh.2.le]
  rw [he]
  have hh := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ E)
    (fun p _ _ => cappedPowerAbove_nonnegative hA hAB h[p])
  exact hh.trans_eq (sum_schedule_values (cappedPowerAbove A B) h)

theorem eligible_power_sum_rank_bound {A B cap : ℝ} (hA : 0 < A) (hAB : A ≤ B) (hcap : B ≤ cap)
    (h : List ℝ) (R : Finset (Fin h.length)) :
    ((orderedPositions h (eligibleIndices h R A B)).map fun p => (stepAt h p)^nu).sum ≤
      weightedCount h cap*(1+Real.log (B/A)) :=
  (eligible_power_sum_le_moment hA hAB h R).trans (powerMoment_log_bound hA hAB hcap h)

end
end StrongSilver
