-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PaddedTreeUnitGain
import StrongSilver.ActualParentMembership

namespace StrongSilver.ScheduleTree
noncomputable section
set_option maxHeartbeats 3200000

/-- Every original interval is nonterminal or retains the full original
terminal reserve; no intermediate reserve is introduced. -/
theorem reservedNodes_reserve_zero_or_original {κ : ℝ} {t : ScheduleTree} {q : ScheduleTree × ℝ}
    (hq : q ∈ reservedNodes κ t) : q.2 = 0 ∨ q.2 = κ := by
  induction t generalizing κ with
  | leaf hw => simp [reservedNodes] at hq
  | split l b r il ir =>
    simp only [reservedNodes,List.mem_cons,List.mem_append] at hq
    rcases hq with rfl | hl | hr
    · exact Or.inr rfl
    · rcases il hl with he | he <;> exact Or.inl he
    · exact ir hr

theorem parentedNodes_reserve_zero_or_original {κ : ℝ} {t : ScheduleTree} {q : ParentedScheduleNode}
    (hq : q ∈ parentedNodes 0 κ none t) : q.node.reserve = 0 ∨ q.node.reserve = κ := by
  have hn : q.node ∈ (parentedNodes 0 κ none t).map ParentedScheduleNode.node := List.mem_map.mpr ⟨q,hq,rfl⟩
  rw [parentedNodes_erase] at hn
  have hr : (q.node.source,q.node.reserve) ∈ (BinaryForest.labels (indexedTree 0 κ t)).map (fun q => (q.source,q.reserve)) :=
    List.mem_map.mpr ⟨q.node,hn,rfl⟩
  rw [indexedTree_labels_reserves] at hr
  exact reservedNodes_reserve_zero_or_original hr

/-- A terminal interval cannot satisfy padded balance when its selected
time is small compared with the full reserve. -/
theorem padded_terminal_unbalanced {φ : ℝ → ℝ} {P κ δ : ℝ} {t : ScheduleTree}
    (hP : 0 < P) (hκ : 0 ≤ κ) (hzero : φ 0 ≤ 0) (hroot : P < φ t.rootStep)
    (hδ : 0 ≤ δ) (hδmax : δ ≤ 1/4) (hsmall : 5*(φ t.rootStep-P) < κ) :
    ¬ PaddedBalanced φ P κ δ t := by
  intro hb
  let S := paddedInput φ hP hκ hzero t hroot
  have hbal : S.Balanced δ := (paddedInput_balance_iff φ hP hκ hzero t hroot δ).mpr hb
  have hsmall' : 5*S.t < S.reserve := by rw [paddedInput_time,paddedInput_reserve]; exact hsmall
  exact PaddedSplitInput.terminal_unbalanced hδ hδmax hsmall' hbal

end
end StrongSilver.ScheduleTree
