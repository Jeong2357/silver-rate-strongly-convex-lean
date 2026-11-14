-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandReservedPairCount
import StrongSilver.UnreservedOrdinaryPairs
import StrongSilver.BandLinkedNonterminal

namespace StrongSilver
open ScheduleTree BinaryForest Real Filter Set
noncomputable section
set_option maxHeartbeats 6400000

/-- Every surviving actual linked gap pair maps to an adjacent ordinary
pair of the same full-cut reservation, with its exact original phases. -/
theorem eventually_band_reserved_pair_ordinary : ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ y width : ℝ, ∀ n : ℕ, ∀ h : List ℝ,
    0 < κ → 1 < B → B ≤ κ/128 → u ≤ firstAverageLogScale B → 0 < μ → μ*B ≤ 1/2 →
    y ∈ Icc (outerBandLow u) (outerBandHigh u) → ∀ s : BandPairReservation κ B cap μ u y h,
    ∀ q r : LinkedGap, (q,r) ∈ bandPostReservedPairs κ B μ u width n h s.assembly.reserved y →
    ∃ a b : CutPhase, q.phase? = some a ∧ r.phase? = some b ∧
      (a,b) ∈ s.assembly.ordinaryPairs (bandFullCut μ u y h).terminal := by
  classical
  filter_upwards [eventually_band_good_linked_nonterminal,eventually_band_linked_cut_phases] with u hNonterminal hPhases
  intro κ B cap μ y width n h hκ hB hBκ hU hμ hμB hy s q r hp
  have hPost := List.mem_filter.mp hp
  have hPre := List.mem_filter.mp hPost.1
  have hCandidate : PreAvailablePair B μ u width n (q,r) y := of_decide_eq_true hPre.2
  have hAdjacent : (q,r) ∈ adjacentOccurrences (bandLinkedFrontier κ B μ u y h) := hPre.1
  have hMembers := adjacentOccurrences_members hAdjacent
  obtain ⟨p,hpq⟩ := hNonterminal κ B μ y h q hκ hB hBκ hU hμ hμB hMembers.1 hCandidate.1.1.1
  obtain ⟨p',hpr⟩ := hNonterminal κ B μ y h r hκ hB hBκ hU hμ hμB hMembers.2 hCandidate.2.1.1.1
  let a : CutPhase := ⟨q.node.source.word,p.pivot,p.pivotIndex⟩
  let b : CutPhase := ⟨r.node.source.word,p'.pivot,p'.pivotIndex⟩
  have hqa : q.phase? = some a := by simp only [LinkedGap.phase?,hpq,Option.map_some,a]
  have hrb : r.phase? = some b := by simp only [LinkedGap.phase?,hpr,Option.map_some,b]
  have hRflags : optionReserved LinkedGap.phase? s.assembly.reserved q = false ∧
      optionReserved LinkedGap.phase? s.assembly.reserved r = false := by
    have hh : (!optionReserved LinkedGap.phase? s.assembly.reserved q) = true ∧
        (!optionReserved LinkedGap.phase? s.assembly.reserved r) = true := by simpa only [Bool.and_eq_true] using hPost.2
    constructor
    · cases hqR : optionReserved LinkedGap.phase? s.assembly.reserved q <;> simp_all
    · cases hrR : optionReserved LinkedGap.phase? s.assembly.reserved r <;> simp_all
  have hNotA : a ∉ s.assembly.reserved := by
    intro hm
    have hTrue : optionReserved LinkedGap.phase? s.assembly.reserved q = true := by simp [optionReserved,hqa,hm]
    have hFalse := hRflags.1
    rw [hTrue] at hFalse
    cases hFalse
  have hNotB : b ∉ s.assembly.reserved := by
    intro hm
    have hTrue : optionReserved LinkedGap.phase? s.assembly.reserved r = true := by simp [optionReserved,hrb,hm]
    have hFalse := hRflags.2
    rw [hTrue] at hFalse
    cases hFalse
  have hPair := adjacentOccurrences_filterMap LinkedGap.phase? hAdjacent hqa hrb
  have hPhaseEq := hPhases κ B μ y h hB hU hμ hμB hy
  change (bandLinkedFrontier κ B μ u y h).filterMap LinkedGap.phase? = _ at hPhaseEq
  rw [hPhaseEq,← s.phases_eq] at hPair
  exact ⟨a,b,hqa,hrb,s.assembly.adjacent_unreserved_mem _ hNotA hNotB hPair⟩

end
end StrongSilver
