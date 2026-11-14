-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CartesianScheduleTree
import StrongSilver.CutConcatenation
import StrongSilver.NumberedClosedCut

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 2400000

theorem ScheduleCut.gaps_concat_selected (C D : ScheduleCut) (i : ℕ) (b : ℝ) :
    (C.concat (D.prependSelected i b)).gaps = C.gaps++D.gaps := by
  rw [ScheduleCut.concat_before_selected]
  simp only [ScheduleCut.gaps,List.map_append,List.map_cons]
  simp only [List.append_assoc,List.singleton_append,List.cons_append,List.nil_append]

namespace ScheduleTree

def frontier (A : ℝ) : ScheduleTree → List ScheduleTree
  | .leaf h => [.leaf h]
  | .split l b r => if A < b then l.frontier A++r.frontier A else [.split l b r]

theorem split_word_le {l r : ScheduleTree} {b : ℝ} (hc : (ScheduleTree.split l b r).Cartesian)
    (x : ℝ) (hx : x ∈ (ScheduleTree.split l b r).word) : x ≤ b := by
  rcases List.mem_append.mp hx with hx | hx
  · exact (hc.2.2.2.1 x hx).le
  · rcases List.mem_cons.mp hx with hx | hx
    · subst x; exact le_rfl
    · exact hc.2.2.2.2 x hx

/-- Threshold pruning of the actual Cartesian schedule tree gives exactly
the original chronological full-cut gaps, including the terminal gap. -/
theorem threshold_cut_gaps (t : ScheduleTree) (hc : t.Cartesian) {A : ℝ} (hA : 0 ≤ A) (i : ℕ) :
    (cutScheduleFrom (fun _ b => decide (A < b)) i t.word).gaps = (t.frontier A).map word := by
  induction t generalizing i with
  | leaf h =>
    have hn : ∀ b ∈ h, ∀ j : ℕ, decide (A < b) = false := by
      intro b hb j
      exact decide_eq_false (not_lt_of_ge ((hc b hb).trans hA))
    rw [word,cutScheduleFrom_none _ i h hn]
    rfl
  | split l b r il ir =>
    by_cases hb : A < b
    · have hsel : decide (A < b) = true := decide_eq_true hb
      rw [word,cutScheduleFrom_append]
      simp only [cutScheduleFrom,hsel,↓reduceIte,ScheduleCut.gaps_concat_selected,
        frontier,if_pos hb,List.map_append]
      rw [il hc.1,ir hc.2.1]
    · have hall (x : ℝ) (hx : x ∈ (ScheduleTree.split l b r).word) : x ≤ A :=
        (split_word_le hc x hx).trans (le_of_not_gt hb)
      have hn : ∀ x ∈ (ScheduleTree.split l b r).word, ∀ j : ℕ, decide (A < x) = false := by
        intro x hx j
        exact decide_eq_false (not_lt_of_ge (hall x hx))
      rw [cutScheduleFrom_none _ i _ hn]
      simp only [frontier,if_neg hb,List.map_cons,List.map_nil]
      rfl

theorem fullCut_gaps_from_cartesian (h : List ℝ) {A : ℝ} (hA : 0 ≤ A) :
    (fullCut A h).gaps = ((cartesian h).frontier A).map word := by
  calc
    (fullCut A h).gaps = (fullCut A (cartesian h).word).gaps := by rw [cartesian_word]
    _ = _ := threshold_cut_gaps _ (cartesian_valid h) hA 0

end ScheduleTree
end
end StrongSilver
