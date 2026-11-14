-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.UnavailableParentMeaning
import StrongSilver.LinkedFrontierEdges
import StrongSilver.FrozenFrontierIntegral

namespace StrongSilver
open ScheduleTree BinaryForest Real Set MeasureTheory
noncomputable section
set_option maxHeartbeats 6200000

def GoodLinkedRoot (B μ u : ℝ) (q : LinkedGap) : Prop :=
  bandGoodBool B μ u q.node = true ∧ ∃ p, q.parent = some p ∧ bandGoodBool B μ u p = true

def badRootParentIndicator (B μ u : ℝ) (q : LinkedGap) : ℝ := by
  classical
  exact if GoodLinkedRoot B μ u q then 0 else 1

def badRootParentObservable (κ B μ u : ℝ) (h : List ℝ) (y : ℝ) : ℝ :=
  Real.exp (nu*y)*linkedObservable (badRootParentIndicator B μ u) (cappedStep μ B) 0 κ none none (cartesian h) (bandPad u+Real.exp y)

/-- A gap with a bad root or bad parent either existed at the top cut
or was created by a protected unavailable parent. -/
theorem bad_root_parent_pointwise {κ B μ u y top : ℝ} {h : List ℝ}
    (hlo : outerBandLow u < y) (hhi : top+3*visibilitySpacing ≤ outerBandHigh u) :
    badRootParentObservable κ B μ u h y ≤
      frozenFrontierObservable (cappedStep μ B) (bandPad u) κ nu top h y+
        linkedParentObservable (cappedStep μ B) (bandPad u) κ nu (bandUnavailableIndicator B μ u) h y := by
  classical
  let φ := cappedStep μ B
  let P := bandPad u
  let F := bandUnavailableIndicator B μ u
  let xs := linkedFrontier φ (P+Real.exp y) 0 κ none none (cartesian h)
  let frozen := fun q : LinkedGap => if ParentedScheduleNode.parentAbove φ (P+Real.exp top) q.parent then (1:ℝ) else 0
  have hpoint (q : LinkedGap) (hq : q ∈ xs) : badRootParentIndicator B μ u q ≤ frozen q+optionalNodeCharge F q.parent := by
    have hParentNonneg := optionalNodeCharge_nonnegative F (bandUnavailableIndicator_nonnegative B μ u) q.parent
    have hFrozenNonneg : 0 ≤ frozen q := by dsimp only [frozen]; split_ifs <;> norm_num
    by_cases hg : GoodLinkedRoot B μ u q
    · simp only [badRootParentIndicator,if_pos hg]
      exact add_nonneg hFrozenNonneg hParentNonneg
    · simp only [badRootParentIndicator,if_neg hg]
      by_cases hf : ParentedScheduleNode.parentAbove φ (P+Real.exp top) q.parent
      · have he : frozen q = 1 := if_pos hf
        rw [he]
        linarith only [hParentNonneg]
      · cases hp : q.parent with
        | none => simp [ParentedScheduleNode.parentAbove,hp] at hf
        | some p =>
          have hSelected := linkedFrontier_parent_above (show ParentedScheduleNode.parentAbove φ (P+Real.exp y) none from trivial) hq
          rw [hp] at hSelected hf
          change P+Real.exp y < φ p.pivot at hSelected
          change ¬ P+Real.exp top < φ p.pivot at hf
          have hPos : P < φ p.pivot := lt_trans (lt_add_of_pos_right _ (Real.exp_pos _)) hSelected
          have hHeightLow : y < nodePaddedHeight φ P p := by
            apply (Real.lt_log_iff_exp_lt (sub_pos.mpr hPos)).mpr
            linarith only [hSelected]
          have hHeightHigh : nodePaddedHeight φ P p ≤ top := by
            apply (Real.log_le_iff_le_exp (sub_pos.mpr hPos)).mpr
            linarith only [le_of_not_gt hf]
          have hPred : bandProtectedPredicate B μ u p := by
            refine ⟨hPos,hlo.trans hHeightLow,?_⟩
            change nodePaddedHeight φ P p+3*visibilitySpacing ≤ outerBandHigh u
            linarith only [hHeightHigh,hhi]
          have hEdge := linkedFrontier_actual_edge hq hp
          have hBad : ¬ (bandGoodBool B μ u p = true ∧ bandGoodBool B μ u q.node = true) := by
            intro hh
            exact hg ⟨hh.2,p,hp,hh.1⟩
          have hCharge := unavailable_parent_covers_bad_edge hEdge hPred hBad
          have hF : optionalNodeCharge F (some p) = bandUnavailableIndicator B μ u p := by simp only [optionalNodeCharge,hp,F]
          rw [hF]
          linarith only [hCharge,hFrozenNonneg]
  have hSum := List.sum_le_sum hpoint
  simp only [List.sum_map_add] at hSum
  have hScale := mul_le_mul_of_nonneg_left hSum (Real.exp_pos (nu*y)).le
  have hFrozen : (xs.map frozen).sum = (((xs.filter fun q => decide (ParentedScheduleNode.parentAbove φ (P+Real.exp top) q.parent)).length):ℝ) := by
    rw [list_filter_length_real]
    simp only [decide_eq_true_eq,frozen]
  rw [hFrozen] at hScale
  unfold badRootParentObservable frozenFrontierObservable linkedParentObservable
  rw [List.sum_map_mul_left]
  dsimp only [linkedObservable,xs,φ,P,F] at hScale ⊢
  linear_combination hScale

theorem badRootParentObservable_integrable (κ B μ u a b : ℝ) (h : List ℝ) :
    IntervalIntegrable (badRootParentObservable κ B μ u h) volume a b := by
  have hBase := linkedObservable_integrable (badRootParentIndicator B μ u) (cappedStep μ B) 0 κ none none (cartesian h)
    (fun y => bandPad u+Real.exp y) (by fun_prop) a b
  exact hBase.continuousOn_mul (by fun_prop)

end
end StrongSilver
