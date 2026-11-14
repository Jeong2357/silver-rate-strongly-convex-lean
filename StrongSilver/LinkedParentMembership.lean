-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.LinkedFollowingSum

namespace StrongSilver.ScheduleTree
open BinaryForest
noncomputable section
set_option maxHeartbeats 4800000

theorem linkedFrontier_parent_root_or_mem {φ : ℝ → ℝ} {s : ℝ} {start : ℕ} {κ : ℝ}
    {parent following : Option ScheduleNode} {t : ScheduleTree} {q : LinkedGap}
    (hq : q ∈ linkedFrontier φ s start κ parent following t) :
    q.parent = parent ∨ ∃ p, q.parent = some p ∧ p ∈ labels (t.indexedTree start κ) := by
  induction t generalizing start κ parent following with
  | leaf word =>
    simp only [linkedFrontier,List.mem_singleton] at hq
    subst q
    exact Or.inl rfl
  | split l b r il ir =>
    by_cases hb : s < φ b
    · rw [linkedFrontier,if_pos hb,List.mem_append] at hq
      rcases hq with hl | hr
      · rcases il hl with hp | ⟨p,hp,hm⟩
        · exact Or.inr ⟨⟨start,.split l b r,κ⟩,hp,by simp [indexedTree,labels]⟩
        · exact Or.inr ⟨p,hp,by simp only [indexedTree,labels,List.mem_cons,List.mem_append]; exact Or.inr (Or.inl hm)⟩
      · rcases ir hr with hp | ⟨p,hp,hm⟩
        · exact Or.inr ⟨⟨start,.split l b r,κ⟩,hp,by simp [indexedTree,labels]⟩
        · exact Or.inr ⟨p,hp,by simp only [indexedTree,labels,List.mem_cons,List.mem_append]; exact Or.inr (Or.inr hm)⟩
    · rw [linkedFrontier,if_neg hb,List.mem_singleton] at hq
      subst q
      exact Or.inl rfl

/-- When an external parent and every internal pivot are below the top
cut, none of the resulting frontier gaps has a parent above that cut. -/
theorem linkedFrontier_no_parent_above {φ : ℝ → ℝ} {s top : ℝ} {start : ℕ} {κ : ℝ}
    {parent following : Option ScheduleNode} {t : ScheduleTree}
    (hp : ¬ ParentedScheduleNode.parentAbove φ top parent)
    (hn : ∀ p ∈ labels (t.indexedTree start κ), φ p.pivot ≤ top)
    {q : LinkedGap} (hq : q ∈ linkedFrontier φ s start κ parent following t) :
    ¬ ParentedScheduleNode.parentAbove φ top q.parent := by
  rcases linkedFrontier_parent_root_or_mem hq with hh | ⟨p,hh,hm⟩
  · rwa [hh]
  · rw [hh]
    exact not_lt_of_ge (hn p hm)

end
end StrongSilver.ScheduleTree
