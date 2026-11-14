-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PreAvailablePairCount
import StrongSilver.LinkedCutPhases
import StrongSilver.BandPairReservation
import StrongSilver.OptionReservationCount
import StrongSilver.AdjacentReservedLoss

namespace StrongSilver
open ScheduleTree BinaryForest Real Filter Set
noncomputable section
set_option maxHeartbeats 6200000

def bandPostReservedPairs (κ B μ u width : ℝ) (n : ℕ) (h : List ℝ) (R : List CutPhase) (y : ℝ) : List (LinkedGap × LinkedGap) :=
  (bandPreAvailablePairs κ B μ u width n h y).filter fun p =>
    !optionReserved LinkedGap.phase? R p.1 && !optionReserved LinkedGap.phase? R p.2

def postReservedExclusionObservable (κ B μ u width : ℝ) (n : ℕ) (h : List ℝ) (R : List CutPhase) (y : ℝ) : ℝ :=
  Real.exp (nu*y)*(((bandIndexedFrontier κ B μ u y h).length:ℝ)-((bandPostReservedPairs κ B μ u width n h R y).length:ℝ))

def bandAvailabilityEnvelope (κ B cap μ u width : ℝ) (n : ℕ) (h : List ℝ) (y : ℝ) : ℝ :=
  preAvailableExclusionObservable κ B μ u width n h y+32*weightedCount h cap/u

/-- The actual reservation marks no original phase occurrence twice. -/
theorem eventually_band_linked_reservation_count : ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ y : ℝ, ∀ h : List ℝ,
    1 < B → u ≤ firstAverageLogScale B → 0 < μ → μ*B ≤ 1/2 →
    y ∈ Icc (outerBandLow u) (outerBandHigh u) → ∀ s : BandPairReservation κ B cap μ u y h,
    Real.exp (nu*y)*((bandLinkedFrontier κ B μ u y h).map fun q =>
      if optionReserved LinkedGap.phase? s.assembly.reserved q then (1:ℝ) else 0).sum ≤ 16*weightedCount h cap/u := by
  filter_upwards [eventually_band_linked_cut_phases] with u H
  intro κ B cap μ y h hB hU hμ hμB hy s
  have hPhases := H κ B μ y h hB hU hμ hμB hy
  have hNodup : ((bandLinkedFrontier κ B μ u y h).filterMap LinkedGap.phase?).Nodup := by
    rw [show (bandLinkedFrontier κ B μ u y h).filterMap LinkedGap.phase? = (bandFullCut μ u y h).phases from hPhases]
    exact cutScheduleFrom_phases_nodup _ _ _
  have hCount := optionReserved_sum_le LinkedGap.phase? s.assembly.reserved (bandLinkedFrontier κ B μ u y h) hNodup
  have hScale := mul_le_mul_of_nonneg_left hCount (Real.exp_pos (nu*y)).le
  exact hScale.trans s.reserved_weight

/-- Count of actual available pairs after the reservation, dominated
by an explicit source-schedule envelope before integrating. -/
theorem eventually_band_post_reserved_exclusion : ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ y width : ℝ, ∀ n : ℕ, ∀ h : List ℝ,
    1 < B → u ≤ firstAverageLogScale B → 0 < μ → μ*B ≤ 1/2 →
    y ∈ Icc (outerBandLow u) (outerBandHigh u) → ∀ s : BandPairReservation κ B cap μ u y h,
    postReservedExclusionObservable κ B μ u width n h s.assembly.reserved y ≤
      bandAvailabilityEnvelope κ B cap μ u width n h y := by
  filter_upwards [eventually_band_linked_reservation_count] with u H
  intro κ B cap μ y width n h hB hU hμ hμB hy s
  have hR := H κ B cap μ y h hB hU hμ hμB hy s
  have hSub : (bandPreAvailablePairs κ B μ u width n h y).Sublist (adjacentOccurrences (bandLinkedFrontier κ B μ u y h)) := List.filter_sublist
  have hLoss := adjacent_reserved_loss (optionReserved LinkedGap.phase? s.assembly.reserved)
    (bandLinkedFrontier κ B μ u y h) (bandPreAvailablePairs κ B μ u width n h y) hSub
  have hScale := mul_le_mul_of_nonneg_left hLoss (Real.exp_pos (nu*y)).le
  unfold postReservedExclusionObservable bandPostReservedPairs bandAvailabilityEnvelope preAvailableExclusionObservable
  linear_combination hScale+2*hR

end
end StrongSilver
