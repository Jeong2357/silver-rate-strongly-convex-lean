-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandGoodChildGeometry

namespace StrongSilver
open ScheduleTree Real
noncomputable section
set_option maxHeartbeats 4800000

/-- Every bad actual child edge from a good protected parent is paid
by the lower strip, by the far-child mass budget, or by a nearby bad
protected child. -/
theorem band_bad_child_classification {κ B μ u : ℝ} {h : List ℝ} {q : ParentedScheduleNode} {p : ScheduleNode}
    (hμ : 0 < μ) (hμB : μ*B ≤ 1/2)
    (hq : q ∈ parentedNodes 0 κ none (cartesian h)) (hp : q.parent = some p)
    (hgood : bandGoodBool B μ u p = true) (hbad : bandGoodBool B μ u q.node ≠ true)
    (hz : p.reserve = 0) (hsmall : bandPad u ≤ (cappedStep μ B p.pivot-bandPad u)/4) :
    (bandProtectedPredicate B μ u p ∧ nodePaddedHeight (cappedStep μ B) (bandPad u) p ≤ outerBandLow u+bandBinWidth u) ∨
    FarProtectedChild (cappedStep μ B) (bandPad u) (outerBandLow u) (protectedBandHigh u)
      (bandTolerance u) (bandBinWidth u) q ∨
    NearBadChildAt (cappedStep μ B) (bandPad u) κ (outerBandLow u) (outerBandHigh u)
      (bandTolerance u) (bandBinWidth u) (bandEligible μ B u) (cartesian h) q := by
  have hg := (bandGoodBool_iff B μ u p).mp hgood
  have hbal := paddedGood_balanced hg.1
  by_cases hs : nodePaddedHeight (cappedStep μ B) (bandPad u) p ≤ outerBandLow u+bandBinWidth u
  · exact Or.inl ⟨hg.2,hs⟩
  · have hs' := lt_of_not_ge hs
    right
    by_cases hf : cappedStep μ B q.node.pivot ≤ bandPad u+Real.exp (nodePaddedHeight (cappedStep μ B) (bandPad u) p-bandBinWidth u)
    · left
      refine ⟨p,hp,hbal,hz,hsmall,hs',?_,hf⟩
      unfold protectedBandHigh
      linarith only [hg.2.2.2]
    · right
      have hf' := lt_of_not_ge hf
      have hpos : bandPad u < cappedStep μ B q.node.pivot :=
        lt_trans (lt_add_of_pos_right _ (Real.exp_pos _)) hf'
      have hheight : nodePaddedHeight (cappedStep μ B) (bandPad u) p-bandBinWidth u <
          parentedHeight (cappedStep μ B) (bandPad u) q := by
        apply (Real.lt_log_iff_exp_lt (sub_pos.mpr hpos)).mpr
        linarith only [hf']
      have he := parentedNodes_actual_edge hq hp
      have hpMem := parentedNodes_parent_mem hq hp
      have hc := indexedTree_source_cartesian (cartesian_valid h) hpMem
      have hφ := cappedStep_monotone (B:=B) hμ (by linarith only [hμB])
      have horder := actual_child_height_le hφ he hc hpos
      change parentedHeight (cappedStep μ B) (bandPad u) q ≤ nodePaddedHeight (cappedStep μ B) (bandPad u) p at horder
      have hpred : bandProtectedPredicate B μ u q.node := by
        refine ⟨hpos,?_,?_⟩
        · change outerBandLow u < parentedHeight (cappedStep μ B) (bandPad u) q
          linarith only [hs',hheight]
        · change parentedHeight (cappedStep μ B) (bandPad u) q+3*visibilitySpacing ≤ outerBandHigh u
          linarith only [horder,hg.2.2.2]
      have hnotgood : ¬ PaddedGood (cappedStep μ B) (bandPad u) q.node.reserve (bandTolerance u) q.node.source := by
        intro hh
        exact hbad ((bandGoodBool_iff B μ u q.node).mpr ⟨hh,hpred⟩)
      refine ⟨?_,hnotgood,p,hp,?_⟩
      · exact bandProtectedNodes_mem_of_predicate hq hpred
      · linarith only [hheight]

end
end StrongSilver
