-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandReservedPairCount

namespace StrongSilver
open ScheduleTree BinaryForest Real
noncomputable section
set_option maxHeartbeats 3200000

theorem bandPostReservedPairs_adjacent_sublist (κ B μ u width : ℝ) (n : ℕ) (h : List ℝ) (R : List CutPhase) (y : ℝ) :
    (bandPostReservedPairs κ B μ u width n h R y).Sublist (adjacentOccurrences (bandLinkedFrontier κ B μ u y h)) :=
  List.filter_sublist.trans List.filter_sublist

theorem bandPostReservedPairs_pre {κ B μ u width y : ℝ} {n : ℕ} {h : List ℝ} {R : List CutPhase} {p : LinkedGap × LinkedGap}
    (hp : p ∈ bandPostReservedPairs κ B μ u width n h R y) : PreAvailablePair B μ u width n p y :=
  @of_decide_eq_true _ (Classical.propDecidable _) (List.mem_filter.mp (List.mem_filter.mp hp).1).2

theorem adjacent_sublist_fst_sum_le {α : Type*} (F : α → ℝ) (xs : List α) (ps : List (α × α))
    (hSub : ps.Sublist (adjacentOccurrences xs)) (hF : ∀ x, 0 ≤ F x) :
    (ps.map fun p => F p.1).sum ≤ (xs.map F).sum := by
  have hFirst := (hSub.map Prod.fst).trans (adjacentOccurrences_fst_sublist xs)
  have hSum := (hFirst.map F).sum_le_sum (by
    intro z hz
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp hz
    exact hF x)
  simpa only [List.map_map,Function.comp_def] using hSum

end
end StrongSilver
