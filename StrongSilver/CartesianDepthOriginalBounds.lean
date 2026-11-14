-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CartesianCappedTreeMass

namespace StrongSilver.ScheduleTree
noncomputable section
set_option maxHeartbeats 3000000

/-- All chronological depth blocks are actual Cartesian subwords. Each
following pivot is positive, dominates its block, and is no larger than
the original exterior boundary. -/
theorem depthPhases_original_bounds {t : ScheduleTree} (ht : t.Cartesian) {b : ℝ} (hb : 0 < b)
    (hdom : ∀ s ∈ t.word, s ≤ b) (d : ℕ) :
    ∀ q ∈ depthPhases d t b, q.1.Cartesian ∧ q.1.word.Sublist t.word ∧
      (∀ s ∈ q.1.word, s ≤ q.2) ∧ 0 < q.2 ∧ q.2 ≤ b := by
  induction d generalizing t b with
  | zero =>
    intro q hq
    simp only [depthPhases,List.mem_singleton] at hq
    subst q
    exact ⟨ht,List.Sublist.refl _,hdom,hb,le_rfl⟩
  | succ d ih =>
    cases t with
    | leaf h =>
      intro q hq
      simp only [depthPhases,List.mem_singleton] at hq
      subst q
      exact ⟨ht,List.Sublist.refl _,hdom,hb,le_rfl⟩
    | split l p r =>
      have hp : p ≤ b := hdom p (by simp [word])
      have hleftdom : ∀ s ∈ l.word, s ≤ p := fun s hs => (ht.2.2.2.1 s hs).le
      have hrightdom : ∀ s ∈ r.word, s ≤ b := fun s hs => hdom s ((right_word_sublist l r p).subset hs)
      intro q hq
      simp only [depthPhases,List.mem_append] at hq
      rcases hq with hq | hq
      · obtain ⟨hqc,hsub,hqdom,hqpos,hqbound⟩ := ih ht.1 ht.2.2.1 hleftdom q hq
        exact ⟨hqc,hsub.trans (left_word_sublist l r p),hqdom,hqpos,hqbound.trans hp⟩
      · obtain ⟨hqc,hsub,hqdom,hqpos,hqbound⟩ := ih ht.2.1 hb hrightdom q hq
        exact ⟨hqc,hsub.trans (right_word_sublist l r p),hqdom,hqpos,hqbound⟩

namespace FourGapGroup

theorem gap_word_sublist (G : FourGapGroup) (i : Fin 4) : (G.gaps i).Sublist G.tree.word := by
  have hleft := left_word_sublist G.left G.right G.middlePivot
  have hright := right_word_sublist G.left G.right G.middlePivot
  fin_cases i
  · exact (left_word_sublist G.first G.second G.leftPivot).trans hleft
  · exact (right_word_sublist G.first G.second G.leftPivot).trans hleft
  · exact (left_word_sublist G.third G.fourth G.rightPivot).trans hright
  · exact (right_word_sublist G.third G.fourth G.rightPivot).trans hright

theorem internal_pivot_positive {G : FourGapGroup} (h : G.tree.Cartesian) (b : ℝ) (i : Fin 3) :
    0 < G.pivots b i.castSucc := by
  fin_cases i
  · exact h.1.2.2.1
  · exact h.2.2.1
  · exact h.2.1.2.2.1

theorem internal_pivot_mem (G : FourGapGroup) (b : ℝ) (i : Fin 3) : G.pivots b i.castSucc ∈ G.tree.word := by
  fin_cases i
  · change G.leftPivot ∈ (G.first.word++G.leftPivot::G.second.word)++G.middlePivot::(G.third.word++G.rightPivot::G.fourth.word)
    simp
  · change G.middlePivot ∈ G.left.word++G.middlePivot::G.right.word
    simp
  · change G.rightPivot ∈ (G.first.word++G.leftPivot::G.second.word)++G.middlePivot::(G.third.word++G.rightPivot::G.fourth.word)
    simp

end FourGapGroup

end
end StrongSilver.ScheduleTree

namespace StrongSilver
open Scalar.SignedIntervals
noncomputable section

theorem negative_mass_sublist_le {h k : List ℝ} (hs : h.Sublist k) : negativeMass h ≤ negativeMass k := by
  apply (hs.map (fun b => max (-b) 0)).sum_le_sum
  intro x hx
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx
  exact le_max_right _ _

end
end StrongSilver
