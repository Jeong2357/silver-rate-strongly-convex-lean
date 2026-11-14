-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandRootCandidateBudget

namespace StrongSilver
open ScheduleTree BinaryForest Real
noncomputable section
set_option maxHeartbeats 5400000

def bandLinkedFrontier (κ B μ u y : ℝ) (h : List ℝ) : List LinkedGap :=
  linkedFrontier (cappedStep μ B) (bandPad u+Real.exp y) 0 κ none none (cartesian h)

def bandRootCandidateNodes (κ B μ u width : ℝ) (h : List ℝ) (y : ℝ) : List LinkedGap :=
  (bandLinkedFrontier κ B μ u y h).filter fun q => @decide (BandRootCandidate B μ u width q y) (Classical.propDecidable _)

theorem list_length_sub_filter_real {α : Type*} (p : α → Bool) (xs : List α) :
    (xs.length:ℝ)-((xs.filter p).length:ℝ) = (xs.map fun x => if p x then (0:ℝ) else 1).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases hx : p x <;> simp only [List.filter_cons,hx,Bool.false_eq_true,↓reduceIte,List.length_cons,
      List.map_cons,List.sum_cons,Nat.cast_add,Nat.cast_one,ih] <;> linarith only [ih]

theorem bandLinkedFrontier_length (κ B μ u y : ℝ) (h : List ℝ) :
    (bandLinkedFrontier κ B μ u y h).length = (bandIndexedFrontier κ B μ u y h).length := by
  have hh := congrArg List.length (linkedFrontier_erase (cappedStep μ B) (bandPad u+Real.exp y) 0 κ none none (cartesian h))
  simpa only [List.length_map,bandLinkedFrontier,bandIndexedFrontier] using hh

/-- The exclusion observable counts exactly all original gap
occurrences outside the actual S(y), including repeated pivot values. -/
theorem rootCandidateExclusionObservable_eq_count (κ B μ u width y : ℝ) (h : List ℝ) :
    rootCandidateExclusionObservable κ B μ u width h y = Real.exp (nu*y)*
      (((bandIndexedFrontier κ B μ u y h).length:ℝ)-((bandRootCandidateNodes κ B μ u width h y).length:ℝ)) := by
  classical
  have hh := list_length_sub_filter_real
    (fun q : LinkedGap => @decide (BandRootCandidate B μ u width q y) (Classical.propDecidable _)) (bandLinkedFrontier κ B μ u y h)
  simp only [decide_eq_true_eq] at hh
  unfold rootCandidateExclusionObservable linkedDynamicObservable
  change Real.exp (nu*y)*((bandLinkedFrontier κ B μ u y h).map fun q => rootCandidateBadIndicator B μ u width q y).sum = _
  have hEq : ((bandLinkedFrontier κ B μ u y h).map fun q => rootCandidateBadIndicator B μ u width q y).sum =
      ((bandLinkedFrontier κ B μ u y h).length:ℝ)-((bandRootCandidateNodes κ B μ u width h y).length:ℝ) := hh.symm
  rw [hEq,bandLinkedFrontier_length]

end
end StrongSilver
