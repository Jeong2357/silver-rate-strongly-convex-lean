-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FiniteFilteredCount
import StrongSilver.RootCandidateCounts
import StrongSilver.CandidateDepthFailures
import StrongSilver.AdjacentAvailability

namespace StrongSilver
open ScheduleTree BinaryForest Real Set MeasureTheory
noncomputable section
set_option maxHeartbeats 6200000

def PreAvailablePair (B μ u width : ℝ) (n : ℕ) (p : LinkedGap × LinkedGap) (y : ℝ) : Prop :=
  BandRootCandidate B μ u width p.1 y ∧ BandRootCandidate B μ u width p.2 y ∧
    GoodThrough (bandGoodBool B μ u) (n+2) (p.1.node.source.indexedTree p.1.node.start p.1.node.reserve)

def preAvailablePairs (B μ u width : ℝ) (n : ℕ) (qs : List LinkedGap) (y : ℝ) : List (LinkedGap × LinkedGap) :=
  (adjacentOccurrences qs).filter fun p => @decide (PreAvailablePair B μ u width n p y) (Classical.propDecidable _)

def bandPreAvailablePairs (κ B μ u width : ℝ) (n : ℕ) (h : List ℝ) (y : ℝ) : List (LinkedGap × LinkedGap) :=
  preAvailablePairs B μ u width n (bandLinkedFrontier κ B μ u y h) y

def preAvailableExclusionObservable (κ B μ u width : ℝ) (n : ℕ) (h : List ℝ) (y : ℝ) : ℝ :=
  Real.exp (nu*y)*(((bandIndexedFrontier κ B μ u y h).length:ℝ)-((bandPreAvailablePairs κ B μ u width n h y).length:ℝ))

theorem bandRootCandidate_measurableSet (B μ u width : ℝ) (q : LinkedGap) :
    MeasurableSet {y | BandRootCandidate B μ u width q y} := by
  have he : {y | BandRootCandidate B μ u width q y} = {y | rootCandidateBadIndicator B μ u width q y = 0} := by
    ext y
    by_cases hc : BandRootCandidate B μ u width q y <;> simp [rootCandidateBadIndicator,hc]
  rw [he]
  exact measurableSet_eq_fun (rootCandidateBadIndicator_measurable B μ u width q) measurable_const

theorem preAvailablePair_measurableSet (B μ u width : ℝ) (n : ℕ) (p : LinkedGap × LinkedGap) :
    MeasurableSet {y | PreAvailablePair B μ u width n p y} := by
  classical
  by_cases hd : GoodThrough (bandGoodBool B μ u) (n+2) (p.1.node.source.indexedTree p.1.node.start p.1.node.reserve)
  · have he : {y | PreAvailablePair B μ u width n p y} =
        {y | BandRootCandidate B μ u width p.1 y} ∩ {y | BandRootCandidate B μ u width p.2 y} := by ext y; simp [PreAvailablePair,hd]
    rw [he]
    exact (bandRootCandidate_measurableSet B μ u width p.1).inter (bandRootCandidate_measurableSet B μ u width p.2)
  · have he : {y | PreAvailablePair B μ u width n p y} = ∅ := by ext y; simp [PreAvailablePair,hd]
    rw [he]
    exact MeasurableSet.empty

theorem preAvailableExclusionObservable_integrable (κ B μ u width a b : ℝ) (n : ℕ) (h : List ℝ) :
    IntervalIntegrable (preAvailableExclusionObservable κ B μ u width n h) volume a b := by
  let F := fun qs : List LinkedGap => fun y => (qs.length:ℝ)-filteredCount (PreAvailablePair B μ u width n) (adjacentOccurrences qs) y
  have hF (qs : List LinkedGap) : Measurable (F qs) :=
    measurable_const.sub (filteredCount_measurable (PreAvailablePair B μ u width n) (preAvailablePair_measurableSet B μ u width n) _)
  have hFi (qs : List LinkedGap) : IntervalIntegrable (F qs) volume a b :=
    intervalIntegrable_const.sub (filteredCount_integrable (PreAvailablePair B μ u width n) (preAvailablePair_measurableSet B μ u width n) _ a b)
  have hBase := linkedFrontier_general_integrable F hF (cappedStep μ B) (bandPad u) 0 κ none none (cartesian h) a b hFi
  have hWeight := hBase.continuousOn_mul (show ContinuousOn (fun y : ℝ => Real.exp (nu*y)) (uIcc a b) by fun_prop)
  have he : preAvailableExclusionObservable κ B μ u width n h = fun y =>
      Real.exp (nu*y)*F (linkedFrontier (cappedStep μ B) (bandPad u+Real.exp y) 0 κ none none (cartesian h)) y := by
    funext y
    simp only [preAvailableExclusionObservable,bandPreAvailablePairs,preAvailablePairs,filteredCount,F]
    rw [← bandLinkedFrontier_length]
    rfl
  rw [he]
  exact hWeight

end
end StrongSilver
