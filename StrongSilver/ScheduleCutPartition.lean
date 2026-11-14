-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ScheduleCut
import StrongSilver.WeightedCount

namespace StrongSilver
noncomputable section

namespace ScheduleCut

@[simp] theorem gaps_length (C : ScheduleCut) : C.gaps.length = C.phases.length+1 := by
  simp [gaps]

/-- Additive quantities are partitioned without multiplicity loss. -/
theorem word_sum (C : ScheduleCut) (w : ℝ → ℝ) :
    (C.word.map w).sum = (C.unselected.map w).sum + (C.phases.map fun q => w q.pivot).sum := by
  rcases C with ⟨qs,t⟩
  induction qs with
  | nil => simp [word,unselected,gaps]
  | cons q qs ih =>
    simp only [word,unselected,gaps,List.flatMap_cons,List.map_cons,List.cons_append,
      List.flatten_cons,List.map_append,List.sum_append,List.sum_cons,List.sum_singleton,List.map_nil,List.sum_nil,
      CutPhase.word] at ih ⊢
    linarith only [ih]

theorem length_partition (C : ScheduleCut) : C.word.length = C.unselected.length+C.phases.length := by
  have hh := C.word_sum (fun _ => 1)
  simp only [List.map_const',List.sum_replicate,nsmul_eq_mul,mul_one] at hh
  exact_mod_cast hh

theorem mem_word_of_mem_unselected {C : ScheduleCut} {a : ℝ} (ha : a ∈ C.unselected) : a ∈ C.word := by
  rcases C with ⟨qs,t⟩
  simp only [unselected,gaps,List.mem_flatten,List.mem_append,List.mem_map,List.mem_singleton] at ha
  obtain ⟨l,hl,hal⟩ := ha
  rcases hl with ⟨q,hq,rfl⟩ | rfl
  · exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨q,hq,List.mem_append_left _ hal⟩)
  · exact List.mem_append_right _ hal

theorem mem_word_of_mem_pivot {C : ScheduleCut} {q : CutPhase} (hq : q ∈ C.phases) : q.pivot ∈ C.word := by
  exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨q,hq,List.mem_append_right _ (by simp)⟩)

end ScheduleCut

theorem closedCut_count (A : ℝ) (h : List ℝ) : (closedCut A h).phases.length = countAbove h A := by
  suffices hh : ∀ i : ℕ, (cutScheduleFrom (fun _ a => decide (A ≤ a)) i h).phases.length = countAbove h A from hh 0
  induction h with
  | nil => intro i; rfl
  | cons a h ih =>
    intro i
    simp only [cutScheduleFrom,countAbove_cons]
    by_cases ha : A ≤ a
    · simp [ha,ScheduleCut.prependSelected,ih,Nat.add_comm]
    · simp only [ha,decide_false,Bool.false_eq_true,↓reduceIte,zero_add]
      have he : (ScheduleCut.prependUnselected (cutScheduleFrom (fun _ a => decide (A ≤ a)) (i+1) h) a).phases.length =
          (cutScheduleFrom (fun _ a => decide (A ≤ a)) (i+1) h).phases.length := by
        generalize cutScheduleFrom (fun _ a => decide (A ≤ a)) (i+1) h = C
        rcases C with ⟨qs,t⟩
        cases qs <;> rfl
      exact he.trans (ih (i+1))

end
end StrongSilver
