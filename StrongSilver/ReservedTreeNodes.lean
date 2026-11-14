-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CartesianPaddedJumps

namespace StrongSilver.ScheduleTree
noncomputable section
set_option maxHeartbeats 2600000

def rootStep : ScheduleTree → ℝ
  | .leaf _ => 0
  | .split _ b _ => b

@[simp] theorem rootStep_split (l r : ScheduleTree) (b : ℝ) : rootStep (.split l b r) = b := rfl

/-- Each occurrence carries its own terminal reserve. Left subtrees
receive zero and the right spine retains the original reserve. -/
def reservedNodes (κ : ℝ) : ScheduleTree → List (ScheduleTree × ℝ)
  | .leaf _ => []
  | .split l b r => (.split l b r,κ)::(reservedNodes 0 l++reservedNodes κ r)

theorem reservedNodes_step_mem {κ : ℝ} {t : ScheduleTree} {q : ScheduleTree × ℝ}
    (hq : q ∈ t.reservedNodes κ) : q.1.rootStep ∈ t.word := by
  induction t generalizing κ with
  | leaf hw => simp [reservedNodes] at hq
  | split l b r il ir =>
    simp only [reservedNodes,List.mem_cons,List.mem_append] at hq
    rcases hq with rfl | hq | hq
    · simp [rootStep,word]
    · exact (left_word_sublist l r b).subset (il hq)
    · exact (right_word_sublist l r b).subset (ir hq)

theorem reservedNodes_reserve_nonnegative {κ : ℝ} (hκ : 0 ≤ κ) {t : ScheduleTree} {q : ScheduleTree × ℝ}
    (hq : q ∈ t.reservedNodes κ) : 0 ≤ q.2 := by
  induction t generalizing κ with
  | leaf hw => simp [reservedNodes] at hq
  | split l b r il ir =>
    simp only [reservedNodes,List.mem_cons,List.mem_append] at hq
    rcases hq with rfl | hq | hq
    · exact hκ
    · exact il (by norm_num) hq
    · exact ir hκ hq

theorem reservedNodes_internal {κ : ℝ} {t : ScheduleTree} {q : ScheduleTree × ℝ}
    (hq : q ∈ t.reservedNodes κ) : ∃ l r : ScheduleTree, ∃ b : ℝ, q.1 = .split l b r := by
  induction t generalizing κ with
  | leaf hw => simp [reservedNodes] at hq
  | split l b r il ir =>
    simp only [reservedNodes,List.mem_cons,List.mem_append] at hq
    rcases hq with rfl | hq | hq
    · exact ⟨l,r,b,rfl⟩
    · exact il hq
    · exact ir hq

/-- Flattening preserves every split occurrence, including tied pivots. -/
theorem splitSumAbove_eq_node_sum (F : ℝ → ScheduleTree → ℝ) (A κ : ℝ)
    (t : ScheduleTree) (hc : t.Cartesian) :
    splitSumAbove F A κ t =
      ((t.reservedNodes κ).map fun q => if A < q.1.rootStep then F q.2 q.1 else 0).sum := by
  induction t generalizing κ with
  | leaf hw => rfl
  | split l b r il ir =>
    by_cases hb : A < b
    · change (if A < b then F κ (.split l b r)+splitSumAbove F A 0 l+splitSumAbove F A κ r else 0) =
        (if A < b then F κ (.split l b r) else 0)+
          ((reservedNodes 0 l++reservedNodes κ r).map fun q => if A < q.1.rootStep then F q.2 q.1 else 0).sum
      simp only [if_pos hb,List.map_append,List.sum_append,il 0 hc.1,ir κ hc.2.1]
      ring
    · have hz : ((reservedNodes κ (.split l b r)).map
          fun q => if A < q.1.rootStep then F q.2 q.1 else 0).sum = 0 := by
        apply List.sum_eq_zero
        intro x hx
        obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hx
        apply if_neg
        exact not_lt_of_ge ((split_word_le hc _ (reservedNodes_step_mem hq)).trans (le_of_not_gt hb))
      rw [hz,splitSumAbove,if_neg hb]

end
end StrongSilver.ScheduleTree
