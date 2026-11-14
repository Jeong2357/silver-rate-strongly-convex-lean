-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.AdjacentOccurrenceMembership
import StrongSilver.ReservationSublists
import StrongSilver.CompletePairTests

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 6400000

namespace CutAssembly

/-- Every adjacent original pair with two unreserved endpoints occurs
in an ordinary run of the actual retained assembly. -/
theorem adjacent_unreserved_mem (s : CutAssembly) (t : List ℝ) {a b : CutPhase}
    (ha : a ∉ s.reserved) (hb : b ∉ s.reserved)
    (hp : (a,b) ∈ adjacentOccurrences s.phases) : (a,b) ∈ (s.erase t).adjacentOrdinaryPairs := by
  induction s with
  | ordinaryEnd q => simp [phases,adjacentOccurrences] at hp
  | ordinary q s ih =>
    rcases mem_adjacentOccurrences_cons hp with ⟨haq,hhead⟩ | htail
    · subst a
      cases s with
      | ordinaryEnd r =>
        have hr : r = b := Option.some.inj hhead
        subst b
        simp [erase,WorkingAssembly.adjacentOrdinaryPairs]
      | ordinary r s =>
        have hr : r = b := Option.some.inj hhead
        subst b
        simp [erase,WorkingAssembly.adjacentOrdinaryPairs]
      | block r I c s =>
        have hr : r = b := Option.some.inj hhead
        subst b
        exact False.elim (hb (by simp [reserved]))
      | blockEnd r I c =>
        have hr : r = b := Option.some.inj hhead
        subst b
        exact False.elim (hb (by simp [reserved]))
      | noConnector r I =>
        have hr : r = b := Option.some.inj hhead
        subst b
        exact False.elim (hb (by simp [reserved]))
    · have hTail := ih ha hb htail
      exact (WorkingAssembly.adjacentPairs_tail q (s.erase t)).subset hTail
  | block q I c s ih =>
    let R := (CutAssembly.block q I c s).reserved
    let pre := q::(I++[c])
    have hPre : ∀ x ∈ pre, x ∈ R := by
      intro x hx
      simp only [pre,List.mem_cons,List.mem_append,List.mem_singleton] at hx
      dsimp only [R,reserved]
      simp only [List.mem_cons,List.mem_append]
      tauto
    have hPair : (a,b) ∈ adjacentOccurrences (pre++s.phases) := by
      simpa only [pre,phases,List.cons_append,List.append_assoc,List.singleton_append,List.nil_append] using hp
    have hInside := adjacentOccurrences_skip_reserved_prefix R pre s.phases hPre ha hb hPair
    have ha' : a ∉ s.reserved := fun hh => ha (by simp [reserved,hh])
    have hb' : b ∉ s.reserved := fun hh => hb (by simp [reserved,hh])
    exact ih ha' hb' hInside
  | blockEnd q I c => exact False.elim (ha (adjacentOccurrences_members hp).1)
  | noConnector q I => exact False.elim (ha (adjacentOccurrences_members hp).1)

end CutAssembly
namespace CompleteCutAssembly

theorem adjacent_unreserved_mem (s : CompleteCutAssembly) (t : List ℝ) {a b : CutPhase}
    (ha : a ∉ s.reserved) (hb : b ∉ s.reserved)
    (hp : (a,b) ∈ adjacentOccurrences s.phases) : (a,b) ∈ s.ordinaryPairs t := by
  cases s with
  | scalar I => exact False.elim (ha (adjacentOccurrences_members hp).1)
  | positive s => exact s.adjacent_unreserved_mem t ha hb hp
  | leadingBlock I c s =>
    let R := (CompleteCutAssembly.leadingBlock I c s).reserved
    let pre := I++[c]
    have hPre : ∀ x ∈ pre, x ∈ R := by
      intro x hx
      simp only [pre,List.mem_append,List.mem_singleton] at hx
      dsimp only [R,reserved]
      simp only [List.mem_append,List.mem_cons]
      tauto
    have hPair : (a,b) ∈ adjacentOccurrences (pre++s.phases) := by
      simpa only [pre,phases,List.append_assoc,List.singleton_append,List.nil_append] using hp
    have hInside := adjacentOccurrences_skip_reserved_prefix R pre s.phases hPre ha hb hPair
    have ha' : a ∉ s.reserved := fun hh => ha (by simp [reserved,hh])
    have hb' : b ∉ s.reserved := fun hh => hb (by simp [reserved,hh])
    exact s.adjacent_unreserved_mem t ha' hb' hInside
  | leadingEnd I c => exact False.elim (ha (adjacentOccurrences_members hp).1)

end CompleteCutAssembly
end
end StrongSilver
