-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.LinkedFrontier

namespace StrongSilver.ScheduleTree
noncomputable section
set_option maxHeartbeats 5000000

theorem linkedFrontier_first_prefix (φ : ℝ → ℝ) (s : ℝ) (start : ℕ) (κ : ℝ)
    (parent following : Option ScheduleNode) (t : ScheduleTree) :
    ∀ q ∈ (linkedFrontier φ s start κ parent following t).head?, q.node.source.word.IsPrefix t.word := by
  induction t generalizing start κ parent following with
  | leaf word => simp [linkedFrontier]
  | split l b r il ir =>
    simp only [linkedFrontier]
    split_ifs with hb
    · intro q hq
      rw [List.head?_append_of_ne_nil _ (linkedFrontier_nonempty φ s start 0 _ _ l)] at hq
      exact (il _ _ _ _ q hq).trans ⟨b::r.word,rfl⟩
    · simp

/-- The last gap keeps the exact following occurrence and is an
original-word suffix of its source interval. -/
theorem linkedFrontier_last_suffix (φ : ℝ → ℝ) (s : ℝ) (start : ℕ) (κ : ℝ)
    (parent following : Option ScheduleNode) (t : ScheduleTree) :
    ∀ q ∈ (linkedFrontier φ s start κ parent following t).getLast?,
      q.following = following ∧ q.node.source.word.IsSuffix t.word := by
  induction t generalizing start κ parent following with
  | leaf word => simp [linkedFrontier]
  | split l b r il ir =>
    simp only [linkedFrontier]
    split_ifs with hb
    · intro q hq
      rw [List.getLast?_append_of_ne_nil _ (linkedFrontier_nonempty φ s (start+l.word.length+1) κ _ _ r)] at hq
      obtain ⟨hf,hs⟩ := ir _ _ _ _ q hq
      refine ⟨hf,hs.trans ?_⟩
      exact ⟨l.word++[b],by simp [word,List.append_assoc]⟩
    · simp

end
end StrongSilver.ScheduleTree
