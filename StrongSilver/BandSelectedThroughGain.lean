-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandThroughGainEnvelope
import StrongSilver.BandGapDepthComparison

namespace StrongSilver
open ScheduleTree BinaryForest Real
noncomputable section
set_option maxHeartbeats 5800000

/-- The actual good depth prefixes of all available pairs are paid by
one source good-visible-through-depth envelope. -/
theorem band_selected_through_gain (κ B μ u y : ℝ) (h : List ℝ) (R : List CutPhase) :
    Real.exp (nu*y)*((bandPostReservedPairs κ B μ u (Real.log u/200) (fourPhaseDepth u+1) h R y).map fun p =>
      throughSum (fun t => |rootGain (cappedStep μ B) t|) (fourPhaseDepth u+2) p.1.node.source).sum ≤
    linkedGoodThroughObservable κ B μ u (bandGoodGainCharge B μ u) h (fourPhaseDepth u+2) y := by
  classical
  let G := bandGoodBool B μ u
  let F := bandGoodGainCharge B μ u
  let n := fourPhaseDepth u+2
  let ps := bandPostReservedPairs κ B μ u (Real.log u/200) (fourPhaseDepth u+1) h R y
  let qs := bandLinkedFrontier κ B μ u y h
  let Q := fun q : LinkedGap => if GoodLinkedRoot B μ u q then
    Real.exp (nu*y)*goodThroughScore G F n (q.node.source.indexedTree q.node.start q.node.reserve) else 0
  have hQ (q : LinkedGap) : 0 ≤ Q q := by
    dsimp only [Q]
    split_ifs
    · exact mul_nonneg (Real.exp_pos _).le (goodThroughScore_nonnegative G F (bandGoodGainCharge_nonnegative B μ u) _ _)
    · exact le_rfl
  have hSub := bandPostReservedPairs_adjacent_sublist κ B μ u (Real.log u/200) (fourPhaseDepth u+1) h R y
  have hPoint : ∀ p ∈ ps, Real.exp (nu*y)*throughSum (fun t => |rootGain (cappedStep μ B) t|) n p.1.node.source ≤ Q p.1 := by
    intro p hp
    have hPre := bandPostReservedPairs_pre hp
    have hGood : GoodThrough G n (p.1.node.source.indexedTree p.1.node.start p.1.node.reserve) :=
      goodThrough_prefix (k:=1) hPre.2.2
    have hh := goodThrough_indexed_through_sum G (fun t => |rootGain (cappedStep μ B) t|) n p.1.node.start p.1.node.reserve p.1.node.source hGood
    dsimp only [Q]
    rw [if_pos hPre.1.1]
    change Real.exp (nu*y)*throughSum (fun t => |rootGain (cappedStep μ B) t|) n p.1.node.source ≤
      Real.exp (nu*y)*goodThroughScore G (fun q => if G q then |rootGain (cappedStep μ B) q.source| else 0) n _
    rw [hh]
  have hSum := List.sum_le_sum hPoint
  rw [List.sum_map_mul_left] at hSum
  have hAll := adjacent_sublist_fst_sum_le Q qs ps hSub hQ
  have hEq : (qs.map Q).sum = linkedGoodThroughObservable κ B μ u F h n y := by
    rw [linkedGoodThroughObservable_frontier]
  exact hSum.trans (hAll.trans_eq hEq)

end
end StrongSilver
