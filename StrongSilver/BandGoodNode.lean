-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandLowerStripWeight
import StrongSilver.GoodChildCombinatorics

namespace StrongSilver
open ScheduleTree Real
noncomputable section
set_option maxHeartbeats 3600000

def bandProtectedPredicate (B μ u : ℝ) (q : ScheduleNode) : Prop :=
  bandPad u < cappedStep μ B q.pivot ∧ outerBandLow u < nodePaddedHeight (cappedStep μ B) (bandPad u) q ∧
    nodePaddedHeight (cappedStep μ B) (bandPad u) q+3*visibilitySpacing ≤ outerBandHigh u

def bandGoodBool (B μ u : ℝ) (q : ScheduleNode) : Bool := by
  classical
  exact decide (PaddedGood (cappedStep μ B) (bandPad u) q.reserve (bandTolerance u) q.source ∧ bandProtectedPredicate B μ u q)

theorem bandGoodBool_iff (B μ u : ℝ) (q : ScheduleNode) : bandGoodBool B μ u q = true ↔
    PaddedGood (cappedStep μ B) (bandPad u) q.reserve (bandTolerance u) q.source ∧ bandProtectedPredicate B μ u q := by
  classical
  simp only [bandGoodBool,decide_eq_true_eq]

theorem bandProtectedNodes_eq (κ B μ u : ℝ) (h : List ℝ) :
    bandProtectedNodes κ B μ u h = (parentedNodes 0 κ none (cartesian h)).filter
      (fun q => @decide (bandProtectedPredicate B μ u q.node) (Classical.propDecidable _)) := by
  classical
  unfold bandProtectedNodes protectedWindowNodes
  congr 1
  funext q
  apply bool_eq_of_true_iff
  simp only [decide_eq_true_eq]
  constructor
  · intro hh
    exact ⟨hh.1,hh.2.2.1,hh.2.2.2⟩
  · intro hh
    have helig : bandEligible μ B u q.node.pivotIndex q.node.pivot = true := by
      apply decide_eq_true
      refine ⟨hh.1,hh.2.1.le,?_⟩
      change nodePaddedHeight (cappedStep μ B) (bandPad u) q.node ≤ outerBandHigh u
      linarith only [hh.2.2,visibilitySpacing_positive]
    exact ⟨hh.1,helig,hh.2.1,hh.2.2⟩

def bandStripNodeWeight (B μ u : ℝ) (q : ScheduleNode) : ℝ := by
  classical
  exact if bandProtectedPredicate B μ u q ∧ nodePaddedHeight (cappedStep μ B) (bandPad u) q ≤ outerBandLow u+bandBinWidth u
    then Real.exp (nu*nodePaddedHeight (cappedStep μ B) (bandPad u) q) else 0

theorem bandStripNodeWeight_nonnegative (B μ u : ℝ) (q : ScheduleNode) : 0 ≤ bandStripNodeWeight B μ u q := by
  classical
  unfold bandStripNodeWeight
  split_ifs
  · exact (Real.exp_pos _).le
  · exact le_rfl

theorem bandStripNodeWeight_sum (κ B μ u : ℝ) (h : List ℝ) :
    ((parentedNodes 0 κ none (cartesian h)).map fun q => bandStripNodeWeight B μ u q.node).sum =
      ((bandLowerStripNodes κ B μ u h).map fun q => Real.exp (nu*parentedHeight (cappedStep μ B) (bandPad u) q)).sum := by
  classical
  unfold bandLowerStripNodes
  rw [bandProtectedNodes_eq,List.filter_filter,list_filter_sum_eq]
  congr 1
  apply List.map_congr_left
  intro q hq
  simp only [bandStripNodeWeight,Bool.and_eq_true,decide_eq_true_eq]
  simp only [parentedHeight,nodePaddedHeight,nodeHeight,and_comm]
  rfl

end
end StrongSilver
