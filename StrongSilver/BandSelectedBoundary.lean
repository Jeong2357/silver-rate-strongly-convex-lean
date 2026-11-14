-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.InnerBandGeometry
import StrongSilver.BandBoundaryEnvelope
import StrongSilver.BandGapDepthComparison

namespace StrongSilver
open ScheduleTree BinaryForest Real Filter Set
noncomputable section
set_option maxHeartbeats 9500000

theorem bandBoundaryWindow_nonnegative {u : ℝ} (hu : 0 < u) (z y : ℝ) (k : ℕ) : 0 ≤ bandBoundaryWindow u z k y := by
  have hδ : 0 ≤ bandTolerance u := (Real.rpow_pos_of_pos hu _).le
  have hRad : 0 ≤ 22*(k:ℝ)*bandTolerance u := by positivity
  exact exponentialWindow_nonnegative _ _ _ _ (by linarith only [hRad])

/-- Across any subfamily of actual adjacent gaps, the depth-window
boundary errors are dominated by the explicit protected source
boundary envelope, with no occurrence charged more than once. -/
theorem eventually_band_selected_boundary : ∀ᶠ u : ℝ in atTop,
    ∀ κ B μ y : ℝ, ∀ h : List ℝ, ∀ ps : List (LinkedGap × LinkedGap), ∀ k : ℕ,
    1 < B → 0 < μ → μ*B ≤ 1/2 → y ∈ Icc (innerBandLow u) (innerBandHigh u) →
    ps.Sublist (adjacentOccurrences (bandLinkedFrontier κ B μ u y h)) →
    1 ≤ k → k ≤ fourPhaseDepth u+2 →
    Real.exp (nu*y)*(ps.map fun p => bandDepthBoundaryCost B μ u y k p.1.node).sum ≤
      bandBoundaryEnvelope κ B μ u k h y := by
  classical
  filter_upwards [eventually_inner_band_geometry] with u hGeometry
  intro κ B μ y h ps k hB hμ hμB hy hSub hk0 hk
  let φ := cappedStep μ B
  let P := bandPad u
  let H := nodePaddedHeight φ P
  let F := fun b : ScheduleNode => if P < φ b.pivot ∧ |y-H b-(k:ℝ)*Real.log rho| ≤ (k:ℝ)*(11*bandTolerance u)
    then |normalizedNodeDecrease φ P b| else 0
  let Q := fun q : LinkedGap => ((labels (q.node.source.indexedTree q.node.start q.node.reserve)).map F).sum
  have hF (b : ScheduleNode) : 0 ≤ F b := by dsimp only [F]; split_ifs; exact abs_nonneg _; exact le_rfl
  have hQ (q : LinkedGap) : 0 ≤ Q q := by
    apply List.sum_nonneg
    intro x hx
    obtain ⟨b,_,rfl⟩ := List.mem_map.mp hx
    exact hF b
  have hSelected := adjacent_sublist_fst_sum_le Q (bandLinkedFrontier κ B μ u y h) ps hSub hQ
  have hφ := cappedStep_monotone (B:=B) hμ (by linarith only [hμB])
  have hGlobal := linkedFrontier_subtree_sum_le φ hφ (P+Real.exp y) 0 κ none none (cartesian h) (cartesian_valid h) F hF
  have hSelectedWeighted := mul_le_mul_of_nonneg_left (hSelected.trans hGlobal) (Real.exp_pos (nu*y)).le
  have hPoint : ∀ b ∈ labels ((cartesian h).indexedTree 0 κ), Real.exp (nu*y)*F b ≤
      if bandProtectedPredicate B μ u b then |normalizedNodeDecrease φ P b| *bandBoundaryWindow u (H b) k y else 0 := by
    intro b hb
    by_cases hCond : P < φ b.pivot ∧ |y-H b-(k:ℝ)*Real.log rho| ≤ (k:ℝ)*(11*bandTolerance u)
    · have hδ : 0 ≤ bandTolerance u := (Real.rpow_pos_of_pos hGeometry.1 _).le
      have hRad : 0 ≤ (k:ℝ)*bandTolerance u := mul_nonneg (Nat.cast_nonneg _) hδ
      have hStrip : |y-H b-(k:ℝ)*Real.log rho| ≤ 22*(k:ℝ)*bandTolerance u := by
        nlinarith only [hCond.2,hRad]
      have hProtectedHeights := hGeometry.2.2.2.2.2 y (H b) k hy hk hStrip
      have hProtected : bandProtectedPredicate B μ u b := ⟨hCond.1,hProtectedHeights.1,hProtectedHeights.2⟩
      have hDom := bandBoundaryWindow_dominates hGeometry.1 hk0 hCond.2
      have hScale := mul_le_mul_of_nonneg_right hDom (abs_nonneg (normalizedNodeDecrease φ P b))
      dsimp only [F]
      rw [if_pos hCond,if_pos hProtected]
      linear_combination hScale
    · dsimp only [F]
      rw [if_neg hCond,mul_zero]
      split_ifs
      · exact mul_nonneg (abs_nonneg _) (bandBoundaryWindow_nonnegative hGeometry.1 _ _ _)
      · exact le_rfl
  have hSum := List.sum_le_sum hPoint
  rw [List.sum_map_mul_left] at hSum
  have hEq : ((labels ((cartesian h).indexedTree 0 κ)).map fun b =>
      if bandProtectedPredicate B μ u b then |normalizedNodeDecrease φ P b| *bandBoundaryWindow u (H b) k y else 0).sum =
      bandBoundaryEnvelope κ B μ u k h y := by
    rw [← parentedNodes_erase]
    simp only [List.map_map,Function.comp_def]
    unfold bandBoundaryEnvelope
    rw [bandProtectedNodes_eq,list_filter_sum_eq]
    congr 1
    apply List.map_congr_left
    intro q hq
    by_cases hp : bandProtectedPredicate B μ u q.node
    · simp only [if_pos hp,decide_eq_true hp,↓reduceIte]
      rfl
    · simp only [if_neg hp,decide_eq_false hp,Bool.false_eq_true,↓reduceIte]
  rw [hEq] at hSum
  exact hSelectedWeighted.trans hSum

end
end StrongSilver
