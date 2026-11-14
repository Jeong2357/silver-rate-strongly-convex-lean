-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandFullKernelEnvelope
import StrongSilver.BandRefinementIntegral

namespace StrongSilver
open ScheduleTree BinaryForest Real Filter Set MeasureTheory
noncomputable section
set_option maxHeartbeats 6500000

theorem linkedGoodDepthObservable_nonnegative (κ B μ u y : ℝ) (k : ℕ)
    (F : ScheduleNode → ℝ) (h : List ℝ) (hF : ∀ q, 0 ≤ F q) :
    0 ≤ linkedGoodDepthObservable κ B μ u k F h y := by
  classical
  unfold linkedGoodDepthObservable
  apply List.sum_nonneg
  intro x hx
  obtain ⟨q,_,rfl⟩ := List.mem_map.mp hx
  split_ifs
  · exact mul_nonneg (Real.exp_pos _).le (goodDepthSum_nonnegative _ F hF _ _)
  · exact le_rfl

theorem linkedGoodThroughObservable_nonnegative (κ B μ u y : ℝ) (n : ℕ)
    (F : ScheduleNode → ℝ) (h : List ℝ) (hF : ∀ q, 0 ≤ F q) :
    0 ≤ linkedGoodThroughObservable κ B μ u F h n y := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact add_nonneg (linkedGoodDepthObservable_nonnegative κ B μ u y n F h hF) ih

theorem linkedFollowingObservable_nonnegative (φ : ℝ → ℝ) (P κ v y : ℝ)
    (F : ScheduleNode → ℝ) (h : List ℝ) (hF : ∀ q, 0 ≤ F q) :
    0 ≤ linkedFollowingObservable φ P κ v F h y := by
  unfold linkedFollowingObservable
  apply List.sum_nonneg
  intro x hx
  obtain ⟨q,_,rfl⟩ := List.mem_map.mp hx
  apply mul_nonneg (Real.exp_pos _).le
  cases q.following with
  | none => exact le_rfl
  | some p => exact hF p

theorem bandEndpointGainEnvelope_nonnegative (κ B μ u y : ℝ) (h : List ℝ) :
    0 ≤ bandEndpointGainEnvelope κ B μ u h y :=
  add_nonneg (linkedGoodDepthObservable_nonnegative _ _ _ _ _ _ _ _ (bandGoodGainCharge_nonnegative B μ u))
    (linkedGoodDepthObservable_nonnegative _ _ _ _ _ _ _ _ (bandGoodGainCharge_nonnegative B μ u))

theorem bandBoundaryEnvelope_nonnegative {u : ℝ} (hu : 0 < u) (κ B μ y : ℝ) (k : ℕ) (h : List ℝ) :
    0 ≤ bandBoundaryEnvelope κ B μ u k h y := by
  unfold bandBoundaryEnvelope
  apply List.sum_nonneg
  intro x hx
  obtain ⟨q,_,rfl⟩ := List.mem_map.mp hx
  exact mul_nonneg (abs_nonneg _) (bandBoundaryWindow_nonnegative hu _ y k)

theorem bandAvailabilityEnvelope_nonnegative {u : ℝ} (hu : 0 < u) (κ B cap μ width y : ℝ)
    (n : ℕ) (h : List ℝ) : 0 ≤ bandAvailabilityEnvelope κ B cap μ u width n h y := by
  have hSub : (bandPreAvailablePairs κ B μ u width n h y).Sublist
      (adjacentOccurrences (bandLinkedFrontier κ B μ u y h)) := List.filter_sublist
  have hLen := hSub.length_le.trans (by simpa only [List.length_map] using
    (adjacentOccurrences_fst_sublist (bandLinkedFrontier κ B μ u y h)).length_le)
  rw [bandLinkedFrontier_length] at hLen
  have hLenR : ((bandPreAvailablePairs κ B μ u width n h y).length:ℝ) ≤
      ((bandIndexedFrontier κ B μ u y h).length:ℝ) := by exact_mod_cast hLen
  have hW := weightedCount_nonneg h cap
  unfold bandAvailabilityEnvelope preAvailableExclusionObservable
  exact add_nonneg (mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr hLenR)) (by positivity)

theorem bandPairGainEnvelope_nonnegative {C u : ℝ} (hC : 0 < C) (hu : 0 < u)
    (κ B cap μ y : ℝ) (h : List ℝ) : 0 ≤ bandPairGainEnvelope C κ B cap μ u h y := by
  have hW := weightedCount_nonneg h cap
  have hδ : 0 ≤ bandTolerance u := (Real.rpow_pos_of_pos hu _).le
  have hEp := bandEndpointGainEnvelope_nonnegative κ B μ u y h
  have hFo := linkedFollowingObservable_nonnegative (cappedStep μ B) (bandPad u) κ nu y
    (bandGoodDrawdownCharge B μ u) h (bandGoodDrawdownCharge_nonnegative B μ u)
  unfold bandPairGainEnvelope
  have hm : 0 ≤ max (Real.exp (nu*y)*bandPositiveLog κ B μ u y h) 0 := le_max_right _ _
  positivity

theorem bandAvailableKernelEnvelope_nonnegative {C u : ℝ} (hC : 0 < C) (hu : 0 < u)
    (κ B cap μ y : ℝ) (h : List ℝ) : 0 ≤ bandAvailableKernelEnvelope C κ B cap μ u h y := by
  have hCf := split_coefficient_positive
  have hW := weightedCount_nonneg h cap
  have hδ : 0 ≤ bandTolerance u := (Real.rpow_pos_of_pos hu _).le
  have hPair := bandPairGainEnvelope_nonnegative hC hu κ B cap μ y h
  have hThrough := linkedGoodThroughObservable_nonnegative κ B μ u y (fourPhaseDepth u+2)
    (bandGoodGainCharge B μ u) h (bandGoodGainCharge_nonnegative B μ u)
  have hB0 := bandBoundaryEnvelope_nonnegative hu κ B μ y (fourPhaseDepth u) h
  have hB1 := bandBoundaryEnvelope_nonnegative hu κ B μ y (fourPhaseDepth u+1) h
  have hB2 := bandBoundaryEnvelope_nonnegative hu κ B μ y (fourPhaseDepth u+2) h
  unfold bandAvailableKernelEnvelope
  positivity

theorem bandFullKernelEnvelope_nonnegative {C u : ℝ} (hC : 0 < C) (hu : 0 < u)
    (κ B cap μ y : ℝ) (h : List ℝ) : 0 ≤ bandFullKernelEnvelope C κ B cap μ u h y := by
  have hCf := split_coefficient_positive
  have hAvailable := bandAvailableKernelEnvelope_nonnegative hC hu κ B cap μ y h
  have hRef := bandRefinementSavings_nonnegative κ B μ u y h
  have hCount := bandAvailabilityEnvelope_nonnegative hu κ B cap μ (Real.log u/200) y (fourPhaseDepth u+1) h
  unfold bandFullKernelEnvelope
  positivity

end
end StrongSilver
