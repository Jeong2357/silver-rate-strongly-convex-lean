-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CompletePairTests
import StrongSilver.OrdinaryCostBudget

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 5800000

namespace WorkingAssembly

theorem adjacentOrdinaryPairs_tracked {s : WorkingAssembly} {p : CutPhase × CutPhase}
    (hp : p ∈ s.adjacentOrdinaryPairs) : p.1 ∈ s.tracked ∧ p.2 ∈ s.tracked := by
  induction s generalizing p with
  | ordinaryEnd q t => simp [adjacentOrdinaryPairs] at hp
  | ordinary q s ih =>
    have hTail {v : CutPhase × CutPhase} (hv : v ∈ s.adjacentOrdinaryPairs) :
        v.1 ∈ (.ordinary q s : WorkingAssembly).tracked ∧ v.2 ∈ (.ordinary q s : WorkingAssembly).tracked := by
      obtain ⟨h1,h2⟩ := ih hv
      exact ⟨List.mem_cons_of_mem q h1,List.mem_cons_of_mem q h2⟩
    cases s with
    | ordinaryEnd r t =>
      have he : p = (q,r) := List.mem_singleton.mp hp
      subst p
      simp [tracked]
    | ordinary r s =>
      have hh : p = (q,r) ∨ p ∈ (.ordinary r s : WorkingAssembly).adjacentOrdinaryPairs := List.mem_cons.mp hp
      rcases hh with rfl | ht
      · simp [tracked]
      · exact hTail ht
    | block r I c s => exact hTail hp
    | blockEnd r I c t => simp [adjacentOrdinaryPairs] at hp
    | noConnector r I t => simp [adjacentOrdinaryPairs] at hp
  | block q I c s ih => exact ih hp
  | blockEnd q I c t => simp [adjacentOrdinaryPairs] at hp
  | noConnector q I t => simp [adjacentOrdinaryPairs] at hp

end WorkingAssembly
namespace CompleteCutAssembly

theorem ordinaryPairs_good {good : CutPhase → Bool} {s : CompleteCutAssembly} (hs : s.WellFormed good)
    (t : List ℝ) {p : CutPhase × CutPhase} (hp : p ∈ s.ordinaryPairs t) : good p.1 = true ∧ good p.2 = true := by
  cases s with
  | scalar I => simp [ordinaryPairs] at hp
  | positive s =>
    have hTracked := WorkingAssembly.adjacentOrdinaryPairs_tracked hp
    rw [CutAssembly.erase_tracked] at hTracked
    exact ⟨s.tracked_good hs p.1 hTracked.1,s.tracked_good hs p.2 hTracked.2⟩
  | leadingBlock I c s =>
    have hTracked := WorkingAssembly.adjacentOrdinaryPairs_tracked hp
    rw [CutAssembly.erase_tracked] at hTracked
    exact ⟨s.tracked_good hs.2 p.1 hTracked.1,s.tracked_good hs.2 p.2 hTracked.2⟩
  | leadingEnd I c => simp [ordinaryPairs] at hp

end CompleteCutAssembly
end
end StrongSilver
