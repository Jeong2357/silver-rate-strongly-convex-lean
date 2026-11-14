-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.IndexedNodeDistinctness
import StrongSilver.CartesianThresholdCut
import StrongSilver.MaximizingCutRefinement

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 3600000

/-- A sum over all actual gaps, with the absolute end position supplied
for the terminal gap. The reserve belongs only to that terminal gap. -/
def gapObservable (F : ℕ → List ℝ → ℝ → ℝ) (κ : ℝ) (finish : ℕ) (C : ScheduleCut) : ℝ :=
  (C.phases.map fun q => F (q.index-q.gap.length) q.gap 0).sum+
    F (finish-C.terminal.length) C.terminal κ

theorem gapObservable_concat_selected (F : ℕ → List ℝ → ℝ → ℝ) (κ : ℝ)
    (finish i : ℕ) (b : ℝ) (C D : ScheduleCut) :
    gapObservable F κ finish (C.concat (D.prependSelected i b)) =
      gapObservable F 0 i C+gapObservable F κ finish D := by
  simp only [ScheduleCut.concat_before_selected,gapObservable,List.map_append,List.map_cons,List.sum_append,List.sum_cons]
  ring

namespace ScheduleTree

/-- Chronological frontier carrying the original interval positions and
terminal reserves. A value-equal interval is never merged with another. -/
def indexedFrontier (φ : ℝ → ℝ) (s : ℝ) (start : ℕ) (κ : ℝ) : ScheduleTree → List ScheduleNode
  | t@(.leaf _) => [⟨start,t,κ⟩]
  | t@(.split l b r) => if s < φ b then
      indexedFrontier φ s start 0 l++indexedFrontier φ s (start+l.word.length+1) κ r
    else [⟨start,t,κ⟩]

/-- Any functional of positioned gaps can be summed on the indexed
Cartesian frontier or on the actual original cut, with identical result. -/
theorem indexedFrontier_sum (F : ℕ → List ℝ → ℝ → ℝ) (φ : ℝ → ℝ)
    (hφ : Monotone φ) (s : ℝ) (hzero : φ 0 ≤ s) (start : ℕ) (κ : ℝ)
    (t : ScheduleTree) (hc : t.Cartesian) :
    ((indexedFrontier φ s start κ t).map fun q => F q.start q.source.word q.reserve).sum =
      gapObservable F κ (start+t.word.length) (cutScheduleFrom (fun _ b => decide (s < φ b)) start t.word) := by
  induction t generalizing start κ with
  | leaf hw =>
    have hn : ∀ b ∈ hw, ∀ j : ℕ, decide (s < φ b) = false := by
      intro b hb j
      exact decide_eq_false (not_lt_of_ge ((hφ (hc b hb)).trans hzero))
    rw [word,cutScheduleFrom_none _ start hw hn]
    simp only [indexedFrontier,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,gapObservable,zero_add]
    congr 1
    omega
  | split l b r il ir =>
    by_cases hb : s < φ b
    · have hi : start+l.word.length+1+r.word.length = start+(ScheduleTree.split l b r).word.length := by
        simp only [word,List.length_append,List.length_cons]
        omega
      rw [indexedFrontier,if_pos hb,List.map_append,List.sum_append,il start 0 hc.1,ir _ κ hc.2.1,hi]
      rw [word,cutScheduleFrom_append]
      simp only [cutScheduleFrom,decide_eq_true hb,↓reduceIte]
      rw [gapObservable_concat_selected]
    · have hn : ∀ x ∈ (ScheduleTree.split l b r).word, ∀ j : ℕ, decide (s < φ x) = false := by
        intro x hx j
        exact decide_eq_false (not_lt_of_ge ((hφ (split_word_le hc x hx)).trans (le_of_not_gt hb)))
      rw [cutScheduleFrom_none _ start _ hn,indexedFrontier,if_neg hb]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,gapObservable,zero_add]
      congr 1
      omega

end ScheduleTree
end
end StrongSilver
