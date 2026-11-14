-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.LinkedParentMembership
import StrongSilver.ActualScheduleEdges

namespace StrongSilver.ScheduleTree
noncomputable section
set_option maxHeartbeats 5600000

/-- Every linked gap is the original root interval or an actual
immediate Cartesian child interval, including terminal leaf intervals. -/
theorem linkedFrontier_root_or_edge {φ : ℝ → ℝ} {s : ℝ} {start : ℕ} {κ : ℝ}
    {parent following : Option ScheduleNode} {t : ScheduleTree} {q : LinkedGap}
    (hq : q ∈ linkedFrontier φ s start κ parent following t) :
    (q.node = (⟨start,t,κ⟩ : ScheduleNode) ∧ q.parent = parent) ∨
      ∃ p, q.parent = some p ∧ ScheduleChild p q.node := by
  induction t generalizing start κ parent following with
  | leaf word =>
    simp only [linkedFrontier,List.mem_singleton] at hq
    subst q
    exact Or.inl ⟨rfl,rfl⟩
  | split l b r il ir =>
    by_cases hb : s < φ b
    · rw [linkedFrontier,if_pos hb,List.mem_append] at hq
      rcases hq with hl | hr
      · rcases il hl with ⟨hn,hp⟩ | he
        · refine Or.inr ⟨⟨start,.split l b r,κ⟩,hp,?_⟩
          rw [hn]
          exact ⟨l,r,b,rfl,Or.inl ⟨rfl,rfl,rfl⟩⟩
        · exact Or.inr he
      · rcases ir hr with ⟨hn,hp⟩ | he
        · refine Or.inr ⟨⟨start,.split l b r,κ⟩,hp,?_⟩
          rw [hn]
          exact ⟨l,r,b,rfl,Or.inr ⟨rfl,rfl,rfl⟩⟩
        · exact Or.inr he
    · rw [linkedFrontier,if_neg hb,List.mem_singleton] at hq
      subst q
      exact Or.inl ⟨rfl,rfl⟩

theorem linkedFrontier_actual_edge {φ : ℝ → ℝ} {s κ : ℝ} {t : ScheduleTree} {q : LinkedGap} {p : ScheduleNode}
    (hq : q ∈ linkedFrontier φ s 0 κ none none t) (hp : q.parent = some p) : ScheduleChild p q.node := by
  rcases linkedFrontier_root_or_edge hq with ⟨_,hn⟩ | ⟨p',hp',he⟩
  · rw [hn] at hp
    cases hp
  · have hh : p' = p := Option.some.inj (hp'.symm.trans hp)
    exact hh ▸ he

theorem linkedFrontier_parent_above {φ : ℝ → ℝ} {s : ℝ} {start : ℕ} {κ : ℝ}
    {parent following : Option ScheduleNode} {t : ScheduleTree}
    (hp : ParentedScheduleNode.parentAbove φ s parent) {q : LinkedGap}
    (hq : q ∈ linkedFrontier φ s start κ parent following t) : ParentedScheduleNode.parentAbove φ s q.parent := by
  induction t generalizing start κ parent following with
  | leaf word =>
    simp only [linkedFrontier,List.mem_singleton] at hq
    subst q
    exact hp
  | split l b r il ir =>
    by_cases hb : s < φ b
    · rw [linkedFrontier,if_pos hb,List.mem_append] at hq
      rcases hq with hl | hr
      · exact il (parent:=some (⟨start,.split l b r,κ⟩ : ScheduleNode)) hb hl
      · exact ir (parent:=some (⟨start,.split l b r,κ⟩ : ScheduleNode)) hb hr
    · rw [linkedFrontier,if_neg hb,List.mem_singleton] at hq
      subst q
      exact hp

end
end StrongSilver.ScheduleTree
