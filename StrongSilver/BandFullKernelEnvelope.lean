-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandAvailableKernelEnvelope
import StrongSilver.BandExcludedKernel
import StrongSilver.BandAvailabilityBudget

namespace StrongSilver
open ScheduleTree BinaryForest Real Filter Set MeasureTheory
noncomputable section
set_option maxHeartbeats 10000000

def bandFullKernelEnvelope (C κ B cap μ u : ℝ) (h : List ℝ) (y : ℝ) : ℝ :=
  bandAvailableKernelEnvelope C κ B cap μ u h y+
    2*splitCoefficient*Real.exp (nu*y)*bandRefinementSavings κ B μ u y h+
    (153600*splitCoefficient)*(2:ℝ)^fourPhaseDepth u/u*
      bandAvailabilityEnvelope κ B cap μ u (Real.log u/200) (fourPhaseDepth u+1) h y

/-- Combining available pair starts with their exact original
occurrence complement eliminates the reservation before integration. -/
theorem eventually_band_full_kernel_envelope : ∃ C > 0, ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ critical y : ℝ, ∀ h : List ℝ,
    BandSourceData κ B cap μ critical u h → y ∈ Icc (innerBandLow u) (innerBandHigh u) →
    Real.exp (nu*y)*((bandIndexedFrontier κ B μ u y h).map (bandKernelGapPower B μ u y)).sum ≤
      bandFullKernelEnvelope C κ B cap μ u h y := by
  classical
  obtain ⟨C,hC,HA⟩ := eventually_band_available_kernel_envelope
  refine ⟨C,hC,?_⟩
  filter_upwards [HA,eventually_band_excluded_kernel,eventually_band_pair_reservation,
    eventually_band_post_reserved_exclusion,eventually_inner_band_kernel_window,eventually_gt_atTop (0:ℝ)]
    with u hAvailable hExcluded hReservation hExclusion hGeometry hu
  intro κ B cap μ critical y h S hy
  let xs := bandLinkedFrontier κ B μ u y h
  have hOuter := (hGeometry y (fourPhaseDepth u) hy (by omega)).1
  obtain ⟨s⟩ := hReservation κ B cap μ h S.kappa_gt_one S.threshold_gt_one S.threshold_le_cap S.cap_le_kappa S.scale_upper
    S.curvature_lower S.curvature_upper S.curvature_half S.noncritical S.distance_stable y hOuter
  let ps := bandPostReservedPairs κ B μ u (Real.log u/200) (fourPhaseDepth u+1) h s.assembly.reserved y
  let starts := ps.map Prod.fst
  have hPairs := bandPostReservedPairs_adjacent_sublist κ B μ u (Real.log u/200) (fourPhaseDepth u+1) h s.assembly.reserved y
  have hStarts : starts.Sublist xs := (hPairs.map Prod.fst).trans (adjacentOccurrences_fst_sublist xs)
  obtain ⟨es,hPerm⟩ := hStarts.exists_perm_append
  have hEs : es.Subperm xs := (List.sublist_append_right starts es).subperm.trans hPerm.symm.subperm
  have hMapSubperm : (es.map LinkedGap.node).Subperm (xs.map LinkedGap.node) := by
    obtain ⟨zs,hP,hL⟩ := hEs
    exact ⟨zs.map LinkedGap.node,hP.map LinkedGap.node,hL.map LinkedGap.node⟩
  have hErase : xs.map LinkedGap.node = bandIndexedFrontier κ B μ u y h := linkedFrontier_erase _ _ _ _ _ _ _
  rw [hErase] at hMapSubperm
  have hGoodBound := hAvailable κ B cap μ critical y h S hy s
  have hBadBound := hExcluded κ B cap μ critical y h (es.map LinkedGap.node) S hy hMapSubperm
  simp only [List.map_map,Function.comp_def,List.length_map] at hBadBound
  have hBadWeighted := mul_le_mul_of_nonneg_left hBadBound (Real.exp_pos (nu*y)).le
  have hCountNat : xs.length = ps.length+es.length := by
    have hh := hPerm.length_eq
    simpa only [List.length_append,starts,List.length_map] using hh
  have hCountReal : (xs.length:ℝ) = (ps.length:ℝ)+(es.length:ℝ) := by exact_mod_cast hCountNat
  have hCountEq : Real.exp (nu*y)*(es.length:ℝ) =
      postReservedExclusionObservable κ B μ u (Real.log u/200) (fourPhaseDepth u+1) h s.assembly.reserved y := by
    unfold postReservedExclusionObservable
    rw [← bandLinkedFrontier_length]
    change Real.exp (nu*y)*(es.length:ℝ) = Real.exp (nu*y)*((xs.length:ℝ)-(ps.length:ℝ))
    linear_combination -Real.exp (nu*y)*hCountReal
  have hCountBound := hExclusion κ B cap μ y (Real.log u/200) (fourPhaseDepth u+1) h
    S.threshold_gt_one S.scale_upper S.mu_positive S.curvature_half hOuter s
  rw [← hCountEq] at hCountBound
  have hCf := split_coefficient_positive
  have hCountScale := mul_le_mul_of_nonneg_left hCountBound
    (show 0 ≤ (153600*splitCoefficient)*(2:ℝ)^fourPhaseDepth u/u by positivity)
  let F := fun q : LinkedGap => bandKernelGapPower B μ u y q.node
  have hPartition := (hPerm.map F).sum_eq
  simp only [List.map_append,List.sum_append] at hPartition
  have hStartsEq : (starts.map F).sum = (ps.map fun p => bandKernelGapPower B μ u y p.1.node).sum := by
    simp only [starts,List.map_map,Function.comp_def,F]
  rw [hStartsEq] at hPartition
  have hTotal : ((bandIndexedFrontier κ B μ u y h).map (bandKernelGapPower B μ u y)).sum =
      (ps.map fun p => bandKernelGapPower B μ u y p.1.node).sum+(es.map fun q => bandKernelGapPower B μ u y q.node).sum := by
    have he := congrArg (fun qs : List ScheduleNode => (qs.map (bandKernelGapPower B μ u y)).sum) hErase
    simp only [List.map_map,Function.comp_def] at he
    exact he.symm.trans hPartition
  rw [hTotal]
  unfold bandFullKernelEnvelope
  dsimp only [ps] at hGoodBound ⊢
  linear_combination hGoodBound+hBadWeighted+hCountScale

theorem bandFullKernelEnvelope_integrable {C κ B cap μ u a b : ℝ} (h : List ℝ)
    (hB : 1 < B) (hμ : 0 < μ) (hμB : μ*B ≤ 1/2) :
    IntervalIntegrable (bandFullKernelEnvelope C κ B cap μ u h) volume a b := by
  have hh := ((bandAvailableKernelEnvelope_integrable (C:=C) (κ:=κ) (cap:=cap) (u:=u) h hB hμ hμB).add
    ((bandRefinementSavings_weighted_integrable κ B μ u a b h).const_mul (2*splitCoefficient))).add
      ((bandAvailabilityEnvelope_integrable κ B cap μ u (Real.log u/200) a b (fourPhaseDepth u+1) h).const_mul
        ((153600*splitCoefficient)*(2:ℝ)^fourPhaseDepth u/u))
  convert hh using 1
  funext y
  unfold bandFullKernelEnvelope
  ring

end
end StrongSilver
