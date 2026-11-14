-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.AdjacentAvailability

namespace StrongSilver
noncomputable section
variable {α : Type*}
set_option maxHeartbeats 4400000

theorem mem_adjacentOccurrences_cons {a b q : α} {xs : List α}
    (h : (a,b) ∈ adjacentOccurrences (q::xs)) :
    (a = q ∧ xs.head? = some b) ∨ (a,b) ∈ adjacentOccurrences xs := by
  cases xs with
  | nil => simp [adjacentOccurrences] at h
  | cons r rs =>
    simp only [adjacentOccurrences,List.mem_cons,Prod.mk.injEq] at h
    rcases h with ⟨ha,hb⟩ | ht
    · exact Or.inl ⟨ha,by simp only [List.head?_cons,hb]⟩
    · exact Or.inr ht

theorem mem_adjacentOccurrences_of_tail {a b q : α} {xs : List α}
    (h : (a,b) ∈ adjacentOccurrences xs) : (a,b) ∈ adjacentOccurrences (q::xs) := by
  cases xs with
  | nil => simp [adjacentOccurrences] at h
  | cons r rs => exact List.mem_cons_of_mem (q,r) h

theorem adjacentOccurrences_members {a b : α} {xs : List α} (h : (a,b) ∈ adjacentOccurrences xs) : a ∈ xs ∧ b ∈ xs := by
  induction xs with
  | nil => simp [adjacentOccurrences] at h
  | cons q xs ih =>
    rcases mem_adjacentOccurrences_cons h with ⟨ha,hb⟩ | ht
    · constructor
      · exact List.mem_cons.mpr (Or.inl ha)
      · have hm : b ∈ xs := List.mem_of_mem_head? hb
        exact List.mem_cons_of_mem q hm
    · obtain ⟨ha,hb⟩ := ih ht
      exact ⟨List.mem_cons_of_mem q ha,List.mem_cons_of_mem q hb⟩

/-- Two adjacent unreserved entries cannot touch a reserved prefix. -/
theorem adjacentOccurrences_skip_reserved_prefix (R pre tail : List α) {a b : α}
    (hPrefix : ∀ x ∈ pre, x ∈ R) (ha : a ∉ R) (hb : b ∉ R)
    (h : (a,b) ∈ adjacentOccurrences (pre++tail)) : (a,b) ∈ adjacentOccurrences tail := by
  induction pre with
  | nil => exact h
  | cons q qs ih =>
    have hq := hPrefix q (by simp)
    rcases mem_adjacentOccurrences_cons h with ⟨he,_⟩ | ht
    · exact False.elim (ha (he ▸ hq))
    · exact ih (fun x hx => hPrefix x (List.mem_cons_of_mem q hx)) ht

theorem adjacentOccurrences_filterMap {β : Type*} (f : α → Option β) {a b : α} {u v : β} {xs : List α}
    (h : (a,b) ∈ adjacentOccurrences xs) (ha : f a = some u) (hb : f b = some v) :
    (u,v) ∈ adjacentOccurrences (xs.filterMap f) := by
  induction xs with
  | nil => simp [adjacentOccurrences] at h
  | cons q xs ih =>
    rcases mem_adjacentOccurrences_cons h with ⟨hq,hhead⟩ | ht
    · subst q
      cases xs with
      | nil => simp at hhead
      | cons r rs =>
        have hr : r = b := Option.some.inj hhead
        subst r
        simp only [List.filterMap_cons,ha,hb,adjacentOccurrences,List.mem_cons]
        exact Or.inl trivial
    · have hTail := ih ht
      rw [List.filterMap_cons]
      cases hq : f q with
      | none => exact hTail
      | some w => exact mem_adjacentOccurrences_of_tail hTail

end
end StrongSilver
