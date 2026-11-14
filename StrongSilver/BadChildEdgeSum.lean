-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BadChildClassification
import StrongSilver.ParentChargeMultiplicity

namespace StrongSilver
open ScheduleTree Real
noncomputable section
set_option maxHeartbeats 6000000

/-- The bad-edge contribution is bounded by twice the boundary strip
and the actual near/far child charges. All sums retain original
occurrences. -/
theorem band_bad_child_edge_sum (κ B μ u : ℝ) (h : List ℝ)
    (hμ : 0 < μ) (hμB : μ*B ≤ 1/2)
    (HG : ∀ p ∈ BinaryForest.labels ((cartesian h).indexedTree 0 κ), bandGoodBool B μ u p = true →
      p.reserve = 0 ∧ bandPad u ≤ (cappedStep μ B p.pivot-bandPad u)/4) :
    ((parentedNodes 0 κ none (cartesian h)).map
      (badChildEdgeWeight (bandGoodBool B μ u) (fun p => Real.exp (nu*nodePaddedHeight (cappedStep μ B) (bandPad u) p)))).sum ≤
      2*((bandLowerStripNodes κ B μ u h).map fun q => Real.exp (nu*parentedHeight (cappedStep μ B) (bandPad u) q)).sum+
      (((parentedNodes 0 κ none (cartesian h)).filter fun q =>
        @decide (FarProtectedChild (cappedStep μ B) (bandPad u) (outerBandLow u) (protectedBandHigh u)
          (bandTolerance u) (bandBinWidth u) q) (Classical.propDecidable _)).map (parentWeight (cappedStep μ B) (bandPad u))).sum+
      (((parentedNodes 0 κ none (cartesian h)).filter fun q =>
        @decide (NearBadChildAt (cappedStep μ B) (bandPad u) κ (outerBandLow u) (outerBandHigh u)
          (bandTolerance u) (bandBinWidth u) (bandEligible μ B u) (cartesian h) q) (Classical.propDecidable _)).map
        (parentWeight (cappedStep μ B) (bandPad u))).sum := by
  classical
  let φ := cappedStep μ B
  let P := bandPad u
  let xs := parentedNodes 0 κ none (cartesian h)
  let G := bandGoodBool B μ u
  let w := fun p : ScheduleNode => Real.exp (nu*nodePaddedHeight φ P p)
  let F := bandStripNodeWeight B μ u
  let far := fun q => FarProtectedChild φ P (outerBandLow u) (protectedBandHigh u) (bandTolerance u) (bandBinWidth u) q
  let near := fun q => NearBadChildAt φ P κ (outerBandLow u) (outerBandHigh u) (bandTolerance u) (bandBinWidth u) (bandEligible μ B u) (cartesian h) q
  let fc := fun q => if far q then parentWeight φ P q else 0
  let nc := fun q => if near q then parentWeight φ P q else 0
  have hf (q : ParentedScheduleNode) : 0 ≤ fc q := by dsimp only [fc]; split_ifs <;> first | exact parentWeight_nonnegative φ P q | exact le_rfl
  have hn (q : ParentedScheduleNode) : 0 ≤ nc q := by dsimp only [nc]; split_ifs <;> first | exact parentWeight_nonnegative φ P q | exact le_rfl
  have hp (q : ParentedScheduleNode) : 0 ≤ optionalNodeCharge F q.parent :=
    optionalNodeCharge_nonnegative F (bandStripNodeWeight_nonnegative B μ u) q.parent
  have hpoint (q : ParentedScheduleNode) (hq : q ∈ xs) :
      badChildEdgeWeight G w q ≤ optionalNodeCharge F q.parent+fc q+nc q := by
    cases hparent : q.parent with
    | none =>
      have hpn : 0 ≤ optionalNodeCharge F none := by simpa only [hparent] using hp q
      have hz : badChildEdgeWeight G w q = 0 := by simp only [badChildEdgeWeight,hparent]
      rw [hz]
      exact add_nonneg (add_nonneg hpn (hf q)) (hn q)
    | some p =>
      have hpn : 0 ≤ optionalNodeCharge F (some p) := by simpa only [hparent] using hp q
      by_cases hh : G p = true ∧ G q.node ≠ true
      · have hmem := parentedNodes_parent_mem hq hparent
        have hg := HG p hmem hh.1
        have hclass := band_bad_child_classification hμ hμB hq hparent hh.1 hh.2 hg.1 hg.2
        have he : badChildEdgeWeight G w q = w p := by simp only [badChildEdgeWeight,hparent,if_pos hh]
        have hw : parentWeight φ P q = w p := by simp only [parentWeight,hparent,w]
        rw [he]
        rcases hclass with hs | hfar | hnear
        · have hs' : optionalNodeCharge F (some p) = w p := by
            simp only [optionalNodeCharge,hparent,F,bandStripNodeWeight,if_pos hs,w,φ,P]
          rw [hs']
          linarith only [hf q,hn q]
        · have hfc : fc q = w p := by dsimp only [fc]; rw [if_pos hfar,hw]
          rw [hfc]
          linarith only [hpn,hn q]
        · have hnc : nc q = w p := by dsimp only [nc]; rw [if_pos hnear,hw]
          rw [hnc]
          linarith only [hpn,hf q]
      · have hz : badChildEdgeWeight G w q = 0 := by simp only [badChildEdgeWeight,hparent,if_neg hh]
        rw [hz]
        exact add_nonneg (add_nonneg hpn (hf q)) (hn q)
  have hs := List.sum_le_sum hpoint
  simp only [List.sum_map_add] at hs
  have hParent := parent_charge_multiplicity_root F (bandStripNodeWeight_nonnegative B μ u) κ (cartesian h)
  rw [bandStripNodeWeight_sum] at hParent
  have hFar : (xs.map fc).sum = ((xs.filter fun q => decide (far q)).map (parentWeight φ P)).sum := by
    rw [list_filter_sum_eq]
    simp only [decide_eq_true_eq,fc]
  have hNear : (xs.map nc).sum = ((xs.filter fun q => decide (near q)).map (parentWeight φ P)).sum := by
    rw [list_filter_sum_eq]
    simp only [decide_eq_true_eq,nc]
  rw [hFar,hNear] at hs
  change (xs.map (badChildEdgeWeight G w)).sum ≤ _
  dsimp only [xs,F] at hs hParent
  exact hs.trans (by linarith only [hParent])

end
end StrongSilver
