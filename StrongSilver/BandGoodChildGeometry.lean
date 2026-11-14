-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandGoodNode
import StrongSilver.BandUnitPointwise
import StrongSilver.BalancedChildrenInternal
import StrongSilver.BandFarChildrenSum
import StrongSilver.BandNearBadChildRate

namespace StrongSilver
open ScheduleTree Real Filter
noncomputable section
set_option maxHeartbeats 5600000

theorem paddedGood_balanced {φ : ℝ → ℝ} {P κ δ : ℝ} {t : ScheduleTree}
    (H : PaddedGood φ P κ δ t) : PaddedBalanced φ P κ δ t := by
  cases t with
  | leaf hw => exact False.elim H
  | split l b r => exact H.1

theorem bandProtectedPredicate_eligible {B μ u : ℝ} {q : ScheduleNode}
    (H : bandProtectedPredicate B μ u q) : bandEligible μ B u q.pivotIndex q.pivot = true := by
  apply decide_eq_true
  refine ⟨H.1,H.2.1.le,?_⟩
  change nodePaddedHeight (cappedStep μ B) (bandPad u) q ≤ outerBandHigh u
  linarith only [H.2.2,visibilitySpacing_positive]

theorem bandProtectedNodes_mem_of_predicate {κ B μ u : ℝ} {h : List ℝ} {q : ParentedScheduleNode}
    (hq : q ∈ parentedNodes 0 κ none (cartesian h)) (H : bandProtectedPredicate B μ u q.node) :
    q ∈ bandProtectedNodes κ B μ u h := by
  classical
  rw [bandProtectedNodes_eq]
  exact List.mem_filter.mpr ⟨hq,decide_eq_true H⟩

/-- A good occurrence has zero terminal reserve, a small pad, and two
actual internal child intervals. These facts follow from the original
schedule and the band geometry. -/
theorem eventually_band_good_parent_geometry : ∀ᶠ u : ℝ in atTop,
    ∀ κ B μ : ℝ, ∀ h : List ℝ, ∀ p : ScheduleNode,
    0 < κ → 1 < B → B ≤ κ/128 → u ≤ firstAverageLogScale B → 0 < μ → μ*B ≤ 1/2 →
    p ∈ BinaryForest.labels ((cartesian h).indexedTree 0 κ) → bandGoodBool B μ u p = true →
    p.reserve = 0 ∧ bandPad u ≤ (cappedStep μ B p.pivot-bandPad u)/4 ∧
      (match p.source with
       | .leaf _ => True
       | .split l _ r => HasInternalRoot l ∧ HasInternalRoot r) := by
  have ht := tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/10)
  filter_upwards [eventually_band_balanced_nonterminal,eventually_band_pad_small,
    eventually_gt_atTop (0:ℝ),ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/4))]
    with u hNonterminal hPad hu hTol
  intro κ B μ h p hκ hB hBκ hU hμ hμB hp hgood
  have hδ : 0 ≤ bandTolerance u := (Real.rpow_pos_of_pos hu _).le
  have hδmax : bandTolerance u ≤ 1/4 := by simpa only [bandTolerance,neg_div] using hTol.le
  have hg := (bandGoodBool_iff B μ u p).mp hgood
  have hb := paddedGood_balanced hg.1
  have hp' : p ∈ (parentedNodes 0 κ none (cartesian h)).map ParentedScheduleNode.node := by
    rwa [parentedNodes_erase]
  obtain ⟨q,hq,hqp⟩ := List.mem_map.mp hp'
  have hqpred : bandProtectedPredicate B μ u q.node := hqp ▸ hg.2
  have hqb : PaddedBalanced (cappedStep μ B) (bandPad u) q.node.reserve (bandTolerance u) q.node.source := hqp ▸ hb
  have hzq := hNonterminal κ B μ (bandTolerance u) h q hκ hB hBκ hU hμ hμB hδ hδmax hq
    (bandProtectedPredicate_eligible hqpred) hqb
  have hz : p.reserve = 0 := by simpa only [hqp] using hzq
  have he : Real.exp (nodePaddedHeight (cappedStep μ B) (bandPad u) p) = cappedStep μ B p.pivot-bandPad u :=
    Real.exp_log (sub_pos.mpr hg.2.1)
  have hsmall := (hPad.2 _ hg.2.2.1.le).1
  rw [he] at hsmall
  refine ⟨hz,hsmall,?_⟩
  have hc := indexedTree_source_cartesian (cartesian_valid h) hp
  have hφ := cappedStep_monotone (B:=B) hμ (by linarith only [hμB])
  have hzero : cappedStep μ B 0 ≤ 0 := by
    simp only [cappedStep,if_pos (zero_lt_one.trans hB).le,logarithmicStep_zero,le_refl]
  cases hs : p.source with
  | leaf hw => trivial
  | split l b r =>
    have hb' : PaddedBalanced (cappedStep μ B) (bandPad u) 0 (bandTolerance u) (.split l b r) := by
      simpa only [hz,hs] using hb
    have hroot := sub_pos.mpr hb'.root_positive
    have hsmall' : bandPad u < cappedStep μ B b-bandPad u := by
      change bandPad u ≤ (cappedStep μ B p.source.rootStep-bandPad u)/4 at hsmall
      rw [hs,rootStep_split] at hsmall
      have hP := Real.exp_pos ((987:ℝ)/1000*u)
      change 0 < bandPad u at hP
      linarith only [hsmall,hP]
    exact padded_balanced_children_internal hφ (Real.exp_pos _) hzero hδ hδmax (hs ▸ hc) hsmall' hb'

theorem eventually_band_all_good_children_internal : ∀ᶠ u : ℝ in atTop,
    ∀ κ B μ : ℝ, ∀ h : List ℝ,
    0 < κ → 1 < B → B ≤ κ/128 → u ≤ firstAverageLogScale B → 0 < μ → μ*B ≤ 1/2 →
    AllGoodChildrenInternal (bandGoodBool B μ u) 0 κ (cartesian h) := by
  filter_upwards [eventually_band_good_parent_geometry] with u H
  intro κ B μ h hκ hB hBκ hU hμ hμB
  apply allGoodChildrenInternal_of_labels
  intro p hp hg
  exact (H κ B μ h p hκ hB hBκ hU hμ hμB hp hg).2.2

end
end StrongSilver
