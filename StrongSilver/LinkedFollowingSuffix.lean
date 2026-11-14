-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.LinkedFollowingMembership

namespace StrongSilver.ScheduleTree
noncomputable section
set_option maxHeartbeats 5000000

theorem linkedFrontier_following_suffix_or_boundary {φ : ℝ → ℝ} {s : ℝ} {start : ℕ} {κ : ℝ}
    {parent following : Option ScheduleNode} {t : ScheduleTree} {q : LinkedGap} {p : ScheduleNode}
    (hq : q ∈ linkedFrontier φ s start κ parent following t) (hp : q.following = some p) :
    (following = some p ∧ q.node.source.word.IsSuffix t.word) ∨
      ∃ l r : ScheduleTree, ∃ b : ℝ, p.source = .split l b r ∧ q.node.source.word.IsSuffix l.word := by
  induction t generalizing start κ parent following with
  | leaf word =>
    simp only [linkedFrontier,List.mem_singleton] at hq
    subst q
    exact Or.inl ⟨hp,⟨[],rfl⟩⟩
  | split l b r il ir =>
    by_cases hb : s < φ b
    · rw [linkedFrontier,if_pos hb,List.mem_append] at hq
      rcases hq with hl | hr
      · rcases il hl with ⟨hf,hs⟩ | hh
        · have he : (⟨start,.split l b r,κ⟩ : ScheduleNode) = p := Option.some.inj hf
          exact Or.inr ⟨l,r,b,by rw [← he],hs⟩
        · exact Or.inr hh
      · rcases ir hr with ⟨hf,hs⟩ | hh
        · refine Or.inl ⟨hf,hs.trans ?_⟩
          exact ⟨l.word++[b],by simp [word,List.append_assoc]⟩
        · exact Or.inr hh
    · rw [linkedFrontier,if_neg hb,List.mem_singleton] at hq
      subst q
      exact Or.inl ⟨hp,⟨[],rfl⟩⟩

/-- The original word of every nonterminal gap is a suffix of the
left child of its exact following original pivot occurrence. -/
theorem linkedFrontier_following_suffix {φ : ℝ → ℝ} {s κ : ℝ} {t : ScheduleTree} {q : LinkedGap} {p : ScheduleNode}
    (hq : q ∈ linkedFrontier φ s 0 κ none none t) (hp : q.following = some p) :
    ∃ l r : ScheduleTree, ∃ b : ℝ, p.source = .split l b r ∧ q.node.source.word.IsSuffix l.word := by
  rcases linkedFrontier_following_suffix_or_boundary hq hp with ⟨hh,_⟩ | hh
  · cases hh
  · exact hh

end
end StrongSilver.ScheduleTree
