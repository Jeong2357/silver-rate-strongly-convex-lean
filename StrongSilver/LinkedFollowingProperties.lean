-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.LinkedFrontierEdges
import StrongSilver.BandGoodNode

namespace StrongSilver.ScheduleTree
open BinaryForest
noncomputable section
set_option maxHeartbeats 5400000

/-- Every following pivot remains selected at the actual cut. -/
theorem linkedFrontier_following_selected {φ : ℝ → ℝ} {s : ℝ} {start : ℕ} {κ : ℝ}
    {parent following : Option ScheduleNode} {t : ScheduleTree}
    (hf : ∀ p, following = some p → s < φ p.pivot) {q : LinkedGap} {p : ScheduleNode}
    (hq : q ∈ linkedFrontier φ s start κ parent following t) (hp : q.following = some p) : s < φ p.pivot := by
  induction t generalizing start κ parent following with
  | leaf word =>
    simp only [linkedFrontier,List.mem_singleton] at hq
    subst q
    exact hf p hp
  | split l b r il ir =>
    by_cases hb : s < φ b
    · rw [linkedFrontier,if_pos hb,List.mem_append] at hq
      rcases hq with hl | hr
      · apply il (following:=some (⟨start,.split l b r,κ⟩ : ScheduleNode)) _ hl
        intro p' hp'
        have hh : (⟨start,.split l b r,κ⟩ : ScheduleNode) = p' := Option.some.inj hp'
        exact hh ▸ hb
      · exact ir hf hr
    · rw [linkedFrontier,if_neg hb,List.mem_singleton] at hq
      subst q
      exact hf p hp

/-- Only the terminal gap has no following pivot, and it keeps the
original terminal reserve. -/
theorem linkedFrontier_following_none_reserve {φ : ℝ → ℝ} {s : ℝ} {start : ℕ} {κ : ℝ}
    {parent following : Option ScheduleNode} {t : ScheduleTree} {q : LinkedGap}
    (hq : q ∈ linkedFrontier φ s start κ parent following t) (hn : q.following = none) :
    following = none ∧ q.node.reserve = κ := by
  induction t generalizing start κ parent following with
  | leaf word =>
    simp only [linkedFrontier,List.mem_singleton] at hq
    subst q
    exact ⟨hn,rfl⟩
  | split l b r il ir =>
    by_cases hb : s < φ b
    · rw [linkedFrontier,if_pos hb,List.mem_append] at hq
      rcases hq with hl | hr
      · have hh := il hl
        cases hh.1
      · exact ir hr
    · rw [linkedFrontier,if_neg hb,List.mem_singleton] at hq
      subst q
      exact ⟨hn,rfl⟩

theorem linkedFrontier_internal_mem {φ : ℝ → ℝ} {s : ℝ} {start : ℕ} {κ : ℝ}
    {parent following : Option ScheduleNode} {t : ScheduleTree} {q : LinkedGap}
    (hq : q ∈ linkedFrontier φ s start κ parent following t) (hInt : internalNode q.node = true) :
    q.node ∈ labels (t.indexedTree start κ) := by
  induction t generalizing start κ parent following with
  | leaf word =>
    simp only [linkedFrontier,List.mem_singleton] at hq
    subst q
    simp [internalNode] at hInt
  | split l b r il ir =>
    by_cases hb : s < φ b
    · rw [linkedFrontier,if_pos hb,List.mem_append] at hq
      simp only [indexedTree,labels,List.mem_cons,List.mem_append]
      rcases hq with hl | hr
      · exact Or.inr (Or.inl (il hl))
      · exact Or.inr (Or.inr (ir hr))
    · rw [linkedFrontier,if_neg hb,List.mem_singleton] at hq
      subst q
      simp [indexedTree,labels]

theorem bandGoodBool_internal {B μ u : ℝ} {q : ScheduleNode} (hq : bandGoodBool B μ u q = true) : internalNode q = true := by
  have hg := ((bandGoodBool_iff B μ u q).mp hq).1
  cases hs : q.source with
  | leaf word => simp [PaddedGood,hs] at hg
  | split l b r => simp only [internalNode,hs]

end
end StrongSilver.ScheduleTree
