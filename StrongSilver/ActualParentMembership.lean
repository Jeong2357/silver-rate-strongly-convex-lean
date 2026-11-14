-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ActualScheduleEdges

namespace StrongSilver.ScheduleTree
noncomputable section
set_option maxHeartbeats 3400000

theorem parentedNodes_parent_root_or_mem {start : ℕ} {κ : ℝ} {parent : Option ScheduleNode}
    {t : ScheduleTree} {q : ParentedScheduleNode} {p : ScheduleNode}
    (hq : q ∈ parentedNodes start κ parent t) (hp : q.parent = some p) :
    parent = some p ∨ p ∈ BinaryForest.labels (t.indexedTree start κ) := by
  induction t generalizing start κ parent with
  | leaf hw => simp [parentedNodes] at hq
  | split l b r il ir =>
    simp only [parentedNodes,List.mem_cons,List.mem_append] at hq
    rcases hq with rfl | hl | hr
    · exact Or.inl hp
    · rcases il hl with hp' | hp'
      · have he : (⟨start,.split l b r,κ⟩ : ScheduleNode) = p := Option.some.inj hp'
        exact Or.inr (by simp only [indexedTree,BinaryForest.labels,List.mem_cons,List.mem_append]; exact Or.inl he.symm)
      · exact Or.inr (by simp only [indexedTree,BinaryForest.labels,List.mem_cons,List.mem_append]; exact Or.inr (Or.inl hp'))
    · rcases ir hr with hp' | hp'
      · have he : (⟨start,.split l b r,κ⟩ : ScheduleNode) = p := Option.some.inj hp'
        exact Or.inr (by simp only [indexedTree,BinaryForest.labels,List.mem_cons,List.mem_append]; exact Or.inl he.symm)
      · exact Or.inr (by simp only [indexedTree,BinaryForest.labels,List.mem_cons,List.mem_append]; exact Or.inr (Or.inr hp'))

theorem parentedNodes_parent_mem {κ : ℝ} {t : ScheduleTree} {q : ParentedScheduleNode} {p : ScheduleNode}
    (hq : q ∈ parentedNodes 0 κ none t) (hp : q.parent = some p) : p ∈ BinaryForest.labels (t.indexedTree 0 κ) := by
  rcases parentedNodes_parent_root_or_mem hq hp with hn | hm
  · cases hn
  · exact hm

theorem indexedTree_reserve_nonnegative {start : ℕ} {κ : ℝ} {t : ScheduleTree} {q : ScheduleNode}
    (hκ : 0 ≤ κ) (hq : q ∈ BinaryForest.labels (t.indexedTree start κ)) : 0 ≤ q.reserve := by
  have hh : (q.source,q.reserve) ∈ (BinaryForest.labels (t.indexedTree start κ)).map (fun q => (q.source,q.reserve)) :=
    List.mem_map.mpr ⟨q,hq,rfl⟩
  rw [indexedTree_labels_reserves] at hh
  exact reservedNodes_reserve_nonnegative hκ hh

/-- Original Cartesian order on an actual child edge, including leaves. -/
theorem actual_child_pivot_le {p c : ScheduleNode} (he : ScheduleChild p c) (hp : p.source.Cartesian) : c.pivot ≤ p.pivot := by
  obtain ⟨l,r,b,hs,hl | hr⟩ := he
  · have hc : (ScheduleTree.split l b r).Cartesian := hs ▸ hp
    rw [ScheduleNode.pivot,ScheduleNode.pivot,hl.1,hs,rootStep_split]
    cases l with
    | leaf hw => exact hc.2.2.1.le
    | split ll lb lr =>
      exact (hc.2.2.2.1 lb (by simp [word])).le
  · have hc : (ScheduleTree.split l b r).Cartesian := hs ▸ hp
    rw [ScheduleNode.pivot,ScheduleNode.pivot,hr.1,hs,rootStep_split]
    cases r with
    | leaf hw => exact hc.2.2.1.le
    | split rl rb rr =>
      exact hc.2.2.2.2 rb (by simp [word])

theorem actual_child_height_le {φ : ℝ → ℝ} {P : ℝ} {p c : ScheduleNode}
    (hφ : Monotone φ) (he : ScheduleChild p c) (hp : p.source.Cartesian) (hc : P < φ c.pivot) :
    nodeHeight φ P (c.source,c.reserve) ≤ nodeHeight φ P (p.source,p.reserve) :=
  Real.log_le_log (sub_pos.mpr hc) (sub_le_sub_right (hφ (actual_child_pivot_le he hp)) P)

end
end StrongSilver.ScheduleTree
