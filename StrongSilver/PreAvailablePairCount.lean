-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PreAvailablePairs

namespace StrongSilver
open ScheduleTree BinaryForest Real
noncomputable section
set_option maxHeartbeats 6200000

/-- Before the finite reservation, candidate failure and the complete
depth failure are the only exclusions from adjacent gap pairs. -/
theorem preAvailable_exclusion_pointwise (κ B μ u width : ℝ) (n : ℕ) (h : List ℝ) (y : ℝ) :
    preAvailableExclusionObservable κ B μ u width n h y ≤ Real.exp (nu*y)+
      2*rootCandidateExclusionObservable κ B μ u width h y+candidateDepthFailureObservable κ B μ u width n h y := by
  classical
  let xs := bandLinkedFrontier κ B μ u y h
  let good := fun q : LinkedGap => decide (BandRootCandidate B μ u width q y)
  let deep := fun q : LinkedGap => decide (¬ BandRootCandidate B μ u width q y ∨
    GoodThrough (bandGoodBool B μ u) (n+2) (q.node.source.indexedTree q.node.start q.node.reserve))
  have hPair : ((adjacentOccurrences xs).filter (pairAvailable good deep (fun _ => false))) = preAvailablePairs B μ u width n xs y := by
    apply List.filter_congr
    intro p hp
    apply bool_eq_of_true_iff
    simp only [pairAvailable,good,deep,preAvailablePairs,Bool.and_eq_true,Bool.not_false,and_true,decide_eq_true_eq]
    change _ ↔ PreAvailablePair B μ u width n p y
    unfold PreAvailablePair
    tauto
  have hG (q : LinkedGap) : unavailableIndicator good q = rootCandidateBadIndicator B μ u width q y := by
    simp only [unavailableIndicator,good,decide_eq_true_eq,rootCandidateBadIndicator]
  have hD (q : LinkedGap) : unavailableIndicator deep q = candidateDepthBadIndicator B μ u width n q y := by
    by_cases hc : BandRootCandidate B μ u width q y <;>
      by_cases hd : GoodThrough (bandGoodBool B μ u) (n+2) (q.node.source.indexedTree q.node.start q.node.reserve) <;>
      simp [unavailableIndicator,deep,candidateDepthBadIndicator,rootCandidateBadIndicator,hc,hd]
  have hCount := adjacent_availability_count good deep (fun _ => false) xs
  rw [hPair] at hCount
  have hGfun : unavailableIndicator good = fun q => rootCandidateBadIndicator B μ u width q y := funext hG
  have hDfun : unavailableIndicator deep = fun q => candidateDepthBadIndicator B μ u width n q y := funext hD
  rw [hGfun,hDfun] at hCount
  simp only [Bool.false_eq_true,↓reduceIte,List.map_const',List.sum_replicate,nsmul_eq_mul,mul_zero,add_zero] at hCount
  have hScale := mul_le_mul_of_nonneg_left hCount (Real.exp_pos (nu*y)).le
  have hLen := bandLinkedFrontier_length κ B μ u y h
  unfold preAvailableExclusionObservable bandPreAvailablePairs
  rw [← hLen]
  dsimp only [rootCandidateExclusionObservable,candidateDepthFailureObservable,linkedDynamicObservable,xs,bandLinkedFrontier] at hScale ⊢
  linear_combination hScale

end
end StrongSilver
