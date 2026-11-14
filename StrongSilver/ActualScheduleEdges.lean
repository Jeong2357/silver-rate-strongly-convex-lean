-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.LongVisibleNodes
import StrongSilver.PaddedTreeSpacing

namespace StrongSilver
open ScheduleTree
noncomputable section
set_option maxHeartbeats 3600000

/-- An immediate edge with the original positions and the actual
left/right terminal reserve convention. -/
def ScheduleChild (p c : ScheduleNode) : Prop :=
  ∃ l r : ScheduleTree, ∃ b : ℝ, p.source = .split l b r ∧
    ((c.source = l ∧ c.start = p.start ∧ c.reserve = 0) ∨
      (c.source = r ∧ c.start = p.start+l.word.length+1 ∧ c.reserve = p.reserve))

namespace ScheduleTree

theorem parentedNodes_root_or_edge {start : ℕ} {κ : ℝ} {parent : Option ScheduleNode}
    {t : ScheduleTree} {q : ParentedScheduleNode} (hq : q ∈ parentedNodes start κ parent t) :
    (q.node = (⟨start,t,κ⟩ : ScheduleNode) ∧ q.parent = parent) ∨
      ∃ p : ScheduleNode, q.parent = some p ∧ ScheduleChild p q.node := by
  induction t generalizing start κ parent with
  | leaf hw => simp only [parentedNodes,List.not_mem_nil] at hq
  | split l b r il ir =>
    simp only [parentedNodes,List.mem_cons,List.mem_append] at hq
    rcases hq with rfl | hl | hr
    · exact Or.inl ⟨rfl,rfl⟩
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

theorem parentedNodes_actual_edge {κ : ℝ} {t : ScheduleTree} {q : ParentedScheduleNode} {p : ScheduleNode}
    (hq : q ∈ parentedNodes 0 κ none t) (hp : q.parent = some p) : ScheduleChild p q.node := by
  rcases parentedNodes_root_or_edge hq with ⟨_,hn⟩ | ⟨p',hp',he⟩
  · rw [hn] at hp
    cases hp
  · have hh : p' = p := Option.some.inj (hp'.symm.trans hp)
    exact hh ▸ he

theorem indexedTree_source_cartesian {start : ℕ} {κ : ℝ} {t : ScheduleTree} {q : ScheduleNode}
    (hc : t.Cartesian) (hq : q ∈ BinaryForest.labels (t.indexedTree start κ)) : q.source.Cartesian := by
  induction t generalizing start κ with
  | leaf hw => simp [indexedTree,BinaryForest.labels] at hq
  | split l b r il ir =>
    simp only [indexedTree,BinaryForest.labels,List.mem_cons,List.mem_append] at hq
    rcases hq with rfl | hl | hr
    · exact hc
    · exact il hc.1 hl
    · exact ir hc.2.1 hr

/-- The spacing lemma for either actual immediate edge. -/
theorem actual_balanced_edge_spacing {φ : ℝ → ℝ} {P δ : ℝ} {p c : ScheduleNode}
    (he : ScheduleChild p c) (hP : 0 < P) (hκ : 0 ≤ p.reserve) (hzero : φ 0 ≤ 0)
    (hδ : 0 ≤ δ) (hδmax : δ ≤ 1/100)
    (hp : PaddedBalanced φ P p.reserve δ p.source) (hc : PaddedBalanced φ P c.reserve δ c.source) :
    |nodeHeight φ P (p.source,p.reserve)-nodeHeight φ P (c.source,c.reserve)-Real.log rho| ≤ 11*δ := by
  obtain ⟨l,r,b,hs,hl | hr⟩ := he
  · have hparent : PaddedBalanced φ P p.reserve δ (.split l b r) := hs ▸ hp
    have hchild : PaddedBalanced φ P 0 δ l := by simpa only [hl.1,hl.2.2] using hc
    have hh := padded_balanced_left_spacing hP hκ hzero hδ hδmax hparent hchild
    simpa only [nodeHeight,hs,hl.1,rootStep_split] using hh
  · have hparent : PaddedBalanced φ P p.reserve δ (.split l b r) := hs ▸ hp
    have hchild : PaddedBalanced φ P p.reserve δ r := by simpa only [hr.1,hr.2.2] using hc
    have hh := padded_balanced_right_spacing hP hκ hzero hδ hδmax hparent hchild
    simpa only [nodeHeight,hs,hr.1,rootStep_split] using hh

end ScheduleTree
end
end StrongSilver
