-- SPDX-License-Identifier: GPL-3.0-only
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.Real.Basic

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 1800000

theorem list_filter_sum_eq {α : Type*} (p : α → Bool) (f : α → ℝ) (xs : List α) :
    ((xs.filter p).map f).sum = (xs.map fun x => if p x then f x else 0).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases hx : p x = true
    · simp only [List.filter_cons,hx,↓reduceIte,List.map_cons,List.sum_cons,ih]
    · simp only [List.filter_cons,Bool.eq_false_iff.mpr hx,Bool.false_eq_true,↓reduceIte,List.map_cons,List.sum_cons,zero_add,ih]

theorem list_filtered_sum_domination {α : Type*} (p q : α → Bool) (f g : α → ℝ) (xs : List α)
    (hg : ∀ x ∈ xs, 0 ≤ g x)
    (hfg : ∀ x ∈ xs, p x = true → q x = true ∧ f x ≤ g x) :
    ((xs.filter p).map f).sum ≤ ((xs.filter q).map g).sum := by
  rw [list_filter_sum_eq,list_filter_sum_eq]
  apply List.sum_le_sum
  intro x hx
  by_cases hp : p x = true
  · obtain ⟨hq,hh⟩ := hfg x hx hp
    simpa only [hp,hq,↓reduceIte] using hh
  · rw [if_neg hp]
    split_ifs
    · exact hg x hx
    · exact le_rfl

/-- Membership in a filtered occurrence list retains exactly those
occurrences in the original list; no distinctness assumption is needed. -/
local instance {α : Type*} (x : α) (xs : List α) : Decidable (x ∈ xs) := Classical.propDecidable _

theorem list_sum_if_mem_filter {α : Type*} (p : α → Bool) (f : α → ℝ) (xs : List α) :
    (xs.map fun x => if x ∈ xs.filter p then f x else 0).sum = ((xs.filter p).map f).sum := by
  classical
  rw [list_filter_sum_eq]
  congr 1
  apply List.map_congr_left
  intro x hx
  have hh : x ∈ xs.filter p ↔ p x = true := by simp only [List.mem_filter,hx,true_and]
  simp only [hh]

end
end StrongSilver
