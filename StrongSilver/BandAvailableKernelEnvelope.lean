-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandKernelGapGain
import StrongSilver.BandSelectedThroughGain
import StrongSilver.BandPairGainBudget
import StrongSilver.InnerBandKernelWindow

namespace StrongSilver
open ScheduleTree BinaryForest Real Filter Set MeasureTheory
noncomputable section
set_option maxHeartbeats 10000000

def bandAvailableKernelEnvelope (C κ B cap μ u : ℝ) (h : List ℝ) (y : ℝ) : ℝ :=
  splitCoefficient*bandPairGainEnvelope C κ B cap μ u h y+
    2*splitCoefficient*bandTolerance u*linkedGoodThroughObservable κ B μ u (bandGoodGainCharge B μ u) h (fourPhaseDepth u+2) y+
    384*splitCoefficient*Real.exp (-u/100)*(2:ℝ)^fourPhaseDepth u*weightedCount h cap+
    bandBoundaryEnvelope κ B μ u (fourPhaseDepth u) h y+
    bandBoundaryEnvelope κ B μ u (fourPhaseDepth u+1) h y+
    bandBoundaryEnvelope κ B μ u (fourPhaseDepth u+2) h y

/-- Every actual available gap kernel is paid by an explicit source
envelope, uniformly for the reservation selected at that cutoff. -/
theorem eventually_band_available_kernel_envelope : ∃ C > 0, ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ critical y : ℝ, ∀ h : List ℝ,
    BandSourceData κ B cap μ critical u h → y ∈ Icc (innerBandLow u) (innerBandHigh u) →
    ∀ s : BandPairReservation κ B cap μ u y h,
    Real.exp (nu*y)*((bandPostReservedPairs κ B μ u (Real.log u/200) (fourPhaseDepth u+1) h s.assembly.reserved y).map
      fun p => bandKernelGapPower B μ u y p.1.node).sum ≤ bandAvailableKernelEnvelope C κ B cap μ u h y := by
  obtain ⟨C,hC,HG⟩ := eventually_band_pair_gain_envelope
  refine ⟨C,hC,?_⟩
  filter_upwards [HG,eventually_band_kernel_gap_gain,eventually_band_selected_boundary,eventually_band_top_frontier,
    eventually_inner_band_kernel_window,eventually_inner_band_geometry] with u hGain hKernel hBoundary hTop hWindow hGeometry
  intro κ B cap μ critical y h S hy s
  let d := fourPhaseDepth u
  let ps := bandPostReservedPairs κ B μ u (Real.log u/200) (d+1) h s.assembly.reserved y
  let qs := bandLinkedFrontier κ B μ u y h
  have hSub := bandPostReservedPairs_adjacent_sublist κ B μ u (Real.log u/200) (d+1) h s.assembly.reserved y
  have hOuter := (hWindow y d hy (by omega)).1
  have hCf := split_coefficient_positive
  have hδ : 0 ≤ bandTolerance u := (Real.rpow_pos_of_pos hGeometry.1 _).le
  have hPoint := List.sum_le_sum (fun p (hp : p ∈ ps) => hKernel κ B cap μ critical y h s.assembly.reserved S p.1 p.2 hp)
  simp only [List.sum_map_add,List.sum_map_mul_left,List.map_const',List.sum_replicate,nsmul_eq_mul] at hPoint
  have hWeighted := mul_le_mul_of_nonneg_left hPoint (Real.exp_pos (nu*y)).le
  have hGainBound := mul_le_mul_of_nonneg_left (hGain κ B cap μ critical y h S hOuter s) hCf.le
  have hThrough := mul_le_mul_of_nonneg_left (band_selected_through_gain κ B μ u y h s.assembly.reserved)
    (show 0 ≤ 2*splitCoefficient*bandTolerance u by positivity)
  have hB0 := hBoundary κ B μ y h ps d S.threshold_gt_one S.mu_positive S.curvature_half hy hSub hGeometry.2.1 (by omega)
  have hB1 := hBoundary κ B μ y h ps (d+1) S.threshold_gt_one S.mu_positive S.curvature_half hy hSub (by omega) (by omega)
  have hB2 := hBoundary κ B μ y h ps (d+2) S.threshold_gt_one S.mu_positive S.curvature_half hy hSub (by omega) (by omega)
  have hLen : ps.length ≤ qs.length := hSub.length_le.trans
    (by simpa only [List.length_map] using (adjacentOccurrences_fst_sublist qs).length_le)
  have hLenR : (ps.length:ℝ) ≤ (qs.length:ℝ) := by exact_mod_cast hLen
  have hTopBound := hTop κ B cap μ y h S.threshold_gt_one S.threshold_le_cap S.scale_upper S.mu_positive S.curvature_half hOuter S.threshold_count
  rw [← bandLinkedFrontier_length] at hTopBound
  have hCount := (mul_le_mul_of_nonneg_left hLenR (Real.exp_pos (nu*y)).le).trans hTopBound
  have hCountScale := mul_le_mul_of_nonneg_left hCount
    (show 0 ≤ 96*splitCoefficient*Real.exp (-u/100)*(2:ℝ)^d by positivity)
  dsimp only [ps,d] at hWeighted hB0 hB1 hB2 hCountScale
  unfold bandAvailableKernelEnvelope
  linear_combination hWeighted+hGainBound+hThrough+hB0+hB1+hB2+hCountScale

theorem bandAvailableKernelEnvelope_integrable {C κ B cap μ u a b : ℝ} (h : List ℝ)
    (hB : 1 < B) (hμ : 0 < μ) (hμB : μ*B ≤ 1/2) :
    IntervalIntegrable (bandAvailableKernelEnvelope C κ B cap μ u h) volume a b :=
  ((((((bandPairGainEnvelope_integrable h hB hμ hμB).const_mul splitCoefficient).add
    ((linkedGoodThroughObservable_integrable (bandGoodGainCharge B μ u) h hB hμ hμB (fourPhaseDepth u+2)).const_mul
      (2*splitCoefficient*bandTolerance u))).add intervalIntegrable_const).add
      (bandBoundaryEnvelope_integrable κ B μ u a b (fourPhaseDepth u) h)).add
        (bandBoundaryEnvelope_integrable κ B μ u a b (fourPhaseDepth u+1) h)).add
          (bandBoundaryEnvelope_integrable κ B μ u a b (fourPhaseDepth u+2) h)

end
end StrongSilver
