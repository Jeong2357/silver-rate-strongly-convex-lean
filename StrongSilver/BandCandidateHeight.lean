-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandRootCandidates

namespace StrongSilver
open ScheduleTree BinaryForest Real Filter
noncomputable section
set_option maxHeartbeats 5800000

/-- A good actual frontier root with a good parent lies at most one
silver edge below the current height cutoff. -/
theorem eventually_band_candidate_height : ∀ᶠ u : ℝ in atTop,
    ∀ κ B μ y : ℝ, ∀ h : List ℝ, ∀ q : LinkedGap,
    0 ≤ κ → 1 < B → μ*B ≤ 1/2 →
    q ∈ linkedFrontier (cappedStep μ B) (bandPad u+Real.exp y) 0 κ none none (cartesian h) →
    GoodLinkedRoot B μ u q →
    0 ≤ y-nodePaddedHeight (cappedStep μ B) (bandPad u) q.node ∧
      y-nodePaddedHeight (cappedStep μ B) (bandPad u) q.node ≤ Real.log rho+11*bandTolerance u := by
  filter_upwards [eventually_band_forest_spacing] with u hTol
  intro κ B μ y h q hκ hB hμB hq hGood
  let φ := cappedStep μ B
  let P := bandPad u
  obtain ⟨p,hParent,hParentGood⟩ := hGood.2
  have hGq := (bandGoodBool_iff B μ u q.node).mp hGood.1
  have hGp := (bandGoodBool_iff B μ u p).mp hParentGood
  have hPmem : p ∈ labels ((cartesian h).indexedTree 0 κ) := by
    rcases linkedFrontier_parent_root_or_mem hq with hn | ⟨p',hp',hm⟩
    · rw [hParent] at hn
      cases hn
    · have he : p' = p := Option.some.inj (hp'.symm.trans hParent)
      exact he ▸ hm
  have hReserve := indexedTree_reserve_nonnegative hκ hPmem
  have hEdge := linkedFrontier_actual_edge hq hParent
  have hZero : φ 0 ≤ 0 := by simp only [φ,cappedStep,if_pos (zero_lt_one.trans hB).le,logarithmicStep_zero,le_refl]
  have hSpacing := actual_balanced_edge_spacing hEdge (Real.exp_pos _) hReserve hZero hTol.1 hTol.2.1
    (paddedGood_balanced hGp.1) (paddedGood_balanced hGq.1)
  change |nodePaddedHeight φ P p-nodePaddedHeight φ P q.node-Real.log rho| ≤ 11*bandTolerance u at hSpacing
  have hRootZero : φ 0 ≤ P+Real.exp y := hZero.trans (add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
  have hMem : q.node ∈ indexedFrontier φ (P+Real.exp y) 0 κ (cartesian h) := by
    rw [← linkedFrontier_erase φ (P+Real.exp y) 0 κ none none (cartesian h)]
    exact List.mem_map.mpr ⟨q,hq,rfl⟩
  have hRootUpper := indexedFrontier_root_upper hRootZero hMem
  have hRootHeight : nodePaddedHeight φ P q.node ≤ y := by
    apply (Real.log_le_iff_le_exp (sub_pos.mpr hGq.2.1)).mpr
    change φ q.node.pivot ≤ P+Real.exp y at hRootUpper
    linarith only [hRootUpper]
  have hSelected := linkedFrontier_parent_above (show ParentedScheduleNode.parentAbove φ (P+Real.exp y) none from trivial) hq
  rw [hParent] at hSelected
  change P+Real.exp y < φ p.pivot at hSelected
  have hParentHeight : y < nodePaddedHeight φ P p := by
    apply (Real.lt_log_iff_exp_lt (sub_pos.mpr hGp.2.1)).mpr
    linarith only [hSelected]
  have hUpper := (abs_le.mp hSpacing).2
  dsimp only [φ,P] at hRootHeight hParentHeight hUpper ⊢
  constructor <;> linarith only [hRootHeight,hParentHeight,hUpper]

end
end StrongSilver
