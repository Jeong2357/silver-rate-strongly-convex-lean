-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandKernelApproximation
import StrongSilver.BandOffsetPowerAverage

namespace StrongSilver
open ScheduleTree BinaryForest Real Filter Set
noncomputable section
set_option maxHeartbeats 8000000

/-- The original averaged jump sum is exactly the protected-band
occurrence sum. Its apparent support restriction is derived from the
actual positive pivots and the source cutoff geometry. -/
theorem eventually_band_weighted_jump_support : ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ critical : ℝ, ∀ h : List ℝ,
    BandSourceData κ B cap μ critical u h →
    (((cartesian h).reservedNodes κ).map fun q => smoothedBandWeight u (u/bandRatio) (Real.log q.1.rootStep)*
      paddedRootDecrease (cappedStep μ B) (bandPad u) q.2 q.1).sum = bandWeightedPowerJumps κ B μ u h := by
  classical
  filter_upwards [eventually_band_smoothed_pivot,eventually_inner_band_geometry,eventually_inner_band_kernel_window]
    with u hPivot hGeometry hWindow
  intro κ B cap μ critical h S
  let F := fun q : ScheduleNode => smoothedBandWeight u (u/bandRatio) (Real.log q.pivot)*
    paddedRootDecrease (cappedStep μ B) (bandPad u) q.reserve q.source
  let Fp := fun q : ScheduleTree × ℝ => smoothedBandWeight u (u/bandRatio) (Real.log q.1.rootStep)*
    paddedRootDecrease (cappedStep μ B) (bandPad u) q.2 q.1
  have hErase := congrArg (fun qs : List (ScheduleTree × ℝ) => (qs.map Fp).sum)
    (indexedTree_labels_reserves 0 κ (cartesian h))
  simp only [List.map_map,Function.comp_def] at hErase
  have hParent := congrArg (fun qs : List ScheduleNode => (qs.map F).sum) (parentedNodes_erase 0 κ none (cartesian h))
  simp only [List.map_map,Function.comp_def] at hParent
  have hCore : (((cartesian h).reservedNodes κ).map Fp).sum =
      ((parentedNodes 0 κ none (cartesian h)).map fun q => F q.node).sum := hErase.symm.trans hParent.symm
  change (((cartesian h).reservedNodes κ).map Fp).sum = _
  rw [hCore]
  unfold bandWeightedPowerJumps
  rw [bandProtectedNodes_eq,list_filter_prop_sum_eq]
  congr 1
  apply List.map_congr_left
  intro q hq
  by_cases hp : bandProtectedPredicate B μ u q.node
  · rw [if_pos hp]
  · rw [if_neg hp]
    have hNode : q.node ∈ labels ((cartesian h).indexedTree 0 κ) := by
      rw [← parentedNodes_erase]
      exact List.mem_map.mpr ⟨q,hq,rfl⟩
    have hReserved : (q.node.source,q.node.reserve) ∈ (cartesian h).reservedNodes κ := by
      rw [← indexedTree_labels_reserves 0 κ (cartesian h)]
      exact List.mem_map.mpr ⟨q.node,hNode,rfl⟩
    have hPos : 0 < q.node.pivot := reservedNodes_root_positive (cartesian_valid h) hReserved
    have hZero : smoothedBandWeight u (u/bandRatio) (Real.log q.node.pivot) = 0 := by
      by_contra hn
      obtain ⟨hCap,hActive,hHeight⟩ := hPivot κ B cap μ critical q.node.pivot h S hPos hn
      apply hp
      refine ⟨hActive,hGeometry.2.2.2.1.trans_le hHeight.1,?_⟩
      exact (hWindow (nodePaddedHeight (cappedStep μ B) (bandPad u) q.node) 0 hHeight (by omega)).2.2
    dsimp only [F]
    rw [hZero,zero_mul]

/-- Source Gamma is bounded by the exact protected offset-P jump sum
and the summably small pad-rank correction. -/
theorem eventually_band_gamma_to_jumps : ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ critical : ℝ, ∀ h : List ℝ,
    BandSourceData κ B cap μ critical u h →
    averagedPowerDecrease (cappedStep μ B) κ h u (u/bandRatio) ≤
      bandWeightedPowerJumps κ B μ u h+2*weightedCount h cap*u^(-(1:ℝ)/1000) := by
  filter_upwards [eventually_band_offset_power_average,eventually_band_weighted_jump_support] with u hPad hSupport
  intro κ B cap μ critical h S
  have hh := hPad κ B cap μ critical h S
  rwa [hSupport κ B cap μ critical h S] at hh

end
end StrongSilver
