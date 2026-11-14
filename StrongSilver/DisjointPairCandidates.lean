-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CompleteDisjointReplacement

namespace StrongSilver.WorkingAssembly
noncomputable section
set_option maxHeartbeats 3600000

/-- Adjacent pairs entirely inside an unreserved ordinary run. -/
def adjacentOrdinaryPairs : WorkingAssembly → List (CutPhase × CutPhase)
  | .ordinary q s =>
    (match s with
      | .ordinaryEnd r _ => [(q,r)]
      | .ordinary r _ => [(q,r)]
      | _ => [])++s.adjacentOrdinaryPairs
  | .block _ _ _ s => s.adjacentOrdinaryPairs
  | _ => []

/-- Alternating disjoint matchings on each ordinary run. The two choices
partition all candidate pairs, including runs adjacent to reservations. -/
def alternatingPairs (reset : Bool) : WorkingAssembly → Bool → List (CutPhase × CutPhase)
  | .ordinary q (.ordinaryEnd r _), true => [(q,r)]
  | .ordinary q (.ordinary r s), true => (q,r)::s.alternatingPairs reset true
  | .ordinary _ s, _ => s.alternatingPairs reset true
  | .block _ _ _ s, _ => s.alternatingPairs reset reset
  | _, _ => []

@[simp] theorem alternatingPairs_false (reset : Bool) (q : CutPhase) (s : WorkingAssembly) :
    alternatingPairs reset (.ordinary q s) false = alternatingPairs reset s true := by
  cases s <;> rfl

theorem adjacentPairs_tail (q : CutPhase) (s : WorkingAssembly) :
    s.adjacentOrdinaryPairs.Sublist (WorkingAssembly.ordinary q s).adjacentOrdinaryPairs :=
  List.sublist_append_right _ _

theorem alternatingPairs_sublist (reset take : Bool) (s : WorkingAssembly) :
    (s.alternatingPairs reset take).Sublist s.adjacentOrdinaryPairs := by
  induction s generalizing reset take with
  | ordinaryEnd q t => cases take <;> simp [alternatingPairs,adjacentOrdinaryPairs]
  | ordinary q s ih =>
    cases take with
    | false =>
      rw [alternatingPairs_false]
      exact (ih reset true).trans (adjacentPairs_tail q s)
    | true =>
      cases s with
      | ordinaryEnd r t => simp [alternatingPairs,adjacentOrdinaryPairs]
      | ordinary r s =>
        have hh := ih reset false
        simp only [alternatingPairs] at hh
        exact List.Sublist.cons₂ (q,r) hh
      | block r I c s => exact (ih reset true).trans (adjacentPairs_tail q _)
      | blockEnd r I c t => simp [alternatingPairs,adjacentOrdinaryPairs]
      | noConnector r I t => simp [alternatingPairs,adjacentOrdinaryPairs]
  | block q I c s ih => exact ih reset reset
  | blockEnd q I c t => cases take <;> simp [alternatingPairs,adjacentOrdinaryPairs]
  | noConnector q I t => cases take <;> simp [alternatingPairs,adjacentOrdinaryPairs]

/-- Counting and summing retain occurrence multiplicity; equal-valued
phases at different chronological positions are never identified. -/
theorem alternating_pair_sum (f : CutPhase × CutPhase → ℝ) (s : WorkingAssembly) (take : Bool) :
    ((s.alternatingPairs true take).map f).sum+
      ((s.alternatingPairs false (!take)).map f).sum = (s.adjacentOrdinaryPairs.map f).sum := by
  induction s generalizing take with
  | ordinaryEnd q t => cases take <;> simp [alternatingPairs,adjacentOrdinaryPairs]
  | ordinary q s ih =>
    cases s with
    | ordinaryEnd r t => cases take <;> simp [alternatingPairs,adjacentOrdinaryPairs]
    | ordinary r s =>
      cases take <;> simp only [Bool.not_false,Bool.not_true,alternatingPairs,adjacentOrdinaryPairs,
        List.map_cons,List.sum_cons,List.map_append,List.sum_append,List.map_nil,List.sum_nil,add_zero] at *
      · have hh := ih true
        simp only [alternatingPairs,Bool.not_false,Bool.not_true] at hh
        linarith only [hh]
      · have hh := ih false
        simp only [alternatingPairs,Bool.not_false,Bool.not_true] at hh
        linarith only [hh]
    | block r I c s =>
      cases take <;> simpa only [alternatingPairs,adjacentOrdinaryPairs,List.nil_append] using ih true
    | blockEnd r I c t => cases take <;> simp [alternatingPairs,adjacentOrdinaryPairs]
    | noConnector r I t => cases take <;> simp [alternatingPairs,adjacentOrdinaryPairs]
  | block q I c s ih => simpa only [alternatingPairs,adjacentOrdinaryPairs,Bool.not_true] using ih true
  | blockEnd q I c t => cases take <;> simp [alternatingPairs,adjacentOrdinaryPairs]
  | noConnector q I t => cases take <;> simp [alternatingPairs,adjacentOrdinaryPairs]

end
end StrongSilver.WorkingAssembly
