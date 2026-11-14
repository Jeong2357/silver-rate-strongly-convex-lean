-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.LinkedFollowingProperties

namespace StrongSilver.ScheduleTree
open BinaryForest
noncomputable section
set_option maxHeartbeats 4400000

/-- A following label is the external boundary or an actual original
indexed pivot occurrence. -/
theorem linkedFrontier_following_root_or_mem {φ : ℝ → ℝ} {s : ℝ} {start : ℕ} {κ : ℝ}
    {parent following : Option ScheduleNode} {t : ScheduleTree} {q : LinkedGap} {p : ScheduleNode}
    (hq : q ∈ linkedFrontier φ s start κ parent following t) (hp : q.following = some p) :
    following = some p ∨ p ∈ labels (t.indexedTree start κ) := by
  induction t generalizing start κ parent following with
  | leaf word =>
    simp only [linkedFrontier,List.mem_singleton] at hq
    subst q
    exact Or.inl hp
  | split l b r il ir =>
    by_cases hb : s < φ b
    · rw [linkedFrontier,if_pos hb,List.mem_append] at hq
      rcases hq with hl | hr
      · rcases il hl with hh | hm
        · have he : (⟨start,.split l b r,κ⟩ : ScheduleNode) = p := Option.some.inj hh
          exact Or.inr (by simp only [indexedTree,labels,List.mem_cons,List.mem_append]; exact Or.inl he.symm)
        · exact Or.inr (by simp only [indexedTree,labels,List.mem_cons,List.mem_append]; exact Or.inr (Or.inl hm))
      · rcases ir hr with hh | hm
        · exact Or.inl hh
        · exact Or.inr (by simp only [indexedTree,labels,List.mem_cons,List.mem_append]; exact Or.inr (Or.inr hm))
    · rw [linkedFrontier,if_neg hb,List.mem_singleton] at hq
      subst q
      exact Or.inl hp

theorem linkedFrontier_following_mem {φ : ℝ → ℝ} {s κ : ℝ} {t : ScheduleTree} {q : LinkedGap} {p : ScheduleNode}
    (hq : q ∈ linkedFrontier φ s 0 κ none none t) (hp : q.following = some p) :
    p ∈ labels (t.indexedTree 0 κ) := by
  rcases linkedFrontier_following_root_or_mem hq hp with hh | hm
  · cases hh
  · exact hm

end
end StrongSilver.ScheduleTree
