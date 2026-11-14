-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.LinkedFrontierBoundaries
import StrongSilver.AdjacentOccurrenceMembership

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 6000000

/-- The following pivot is the exact original split occurrence;
neighboring gap words are its left suffix and right prefix. -/
def LinkedFollowingSplit (q r : LinkedGap) : Prop :=
  ∃ p : ScheduleNode, ∃ l r' : ScheduleTree, ∃ b : ℝ,
    q.following = some p ∧ p.source = .split l b r' ∧
      q.node.source.word.IsSuffix l.word ∧ r.node.source.word.IsPrefix r'.word

namespace ScheduleTree

theorem linkedFrontier_adjacent (φ : ℝ → ℝ) (s : ℝ) (start : ℕ) (κ : ℝ)
    (parent following : Option ScheduleNode) (t : ScheduleTree) :
    (linkedFrontier φ s start κ parent following t).IsChain LinkedFollowingSplit := by
  induction t generalizing start κ parent following with
  | leaf word => simp [linkedFrontier]
  | split l b r il ir =>
    simp only [linkedFrontier]
    split_ifs with hb
    · have hL := il start 0 (some (⟨start,.split l b r,κ⟩ : ScheduleNode)) (some (⟨start,.split l b r,κ⟩ : ScheduleNode))
      have hR := ir (start+l.word.length+1) κ (some (⟨start,.split l b r,κ⟩ : ScheduleNode)) following
      apply hL.append hR
      intro q hq q' hq'
      obtain ⟨hf,hs⟩ := linkedFrontier_last_suffix φ s start 0 _ _ l q hq
      have hp := linkedFrontier_first_prefix φ s (start+l.word.length+1) κ _ _ r q' hq'
      exact ⟨⟨start,.split l b r,κ⟩,l,r,b,hf,rfl,hs,hp⟩
    · simp

end ScheduleTree

theorem isChain_rel_of_adjacentOccurrences {α : Type*} {R : α → α → Prop} {xs : List α}
    (hc : xs.IsChain R) {a b : α} (hp : (a,b) ∈ adjacentOccurrences xs) : R a b := by
  induction xs with
  | nil => simp [adjacentOccurrences] at hp
  | cons q xs ih =>
    cases xs with
    | nil => simp [adjacentOccurrences] at hp
    | cons r rs =>
      have hChain : R q r ∧ (r::rs).IsChain R := by simpa only [List.isChain_cons_cons] using hc
      simp only [adjacentOccurrences,List.mem_cons,Prod.mk.injEq] at hp
      rcases hp with ⟨rfl,rfl⟩ | ht
      · exact hChain.1
      · exact ih hChain.2 ht

open ScheduleTree

theorem linkedFrontier_following_split {φ : ℝ → ℝ} {s : ℝ} {start : ℕ} {κ : ℝ}
    {parent following : Option ScheduleNode} {t : ScheduleTree} {q r : LinkedGap}
    (hp : (q,r) ∈ adjacentOccurrences (linkedFrontier φ s start κ parent following t)) :
    LinkedFollowingSplit q r :=
  isChain_rel_of_adjacentOccurrences (linkedFrontier_adjacent φ s start κ parent following t) hp

end
end StrongSilver
