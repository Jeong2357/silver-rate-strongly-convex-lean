-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CutPhaseIndexDistinctness
import StrongSilver.FiniteFilteredSums

namespace StrongSilver
noncomputable section
variable {α β : Type*}
set_option maxHeartbeats 4200000

def optionReserved (f : α → Option β) (R : List β) (x : α) : Bool := by
  classical
  exact match f x with
    | none => false
    | some p => decide (p ∈ R)

theorem optionReserved_filter_length (f : α → Option β) (R : List β) (xs : List α) :
    (xs.filter (optionReserved f R)).length =
      ((xs.filterMap f).filter fun p => @decide (p ∈ R) (Classical.propDecidable _)).length := by
  classical
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases hf : f x with
    | none => simp [optionReserved,hf,ih]
    | some p =>
      by_cases hp : p ∈ R <;> simp [optionReserved,hf,hp,ih]

/-- A reservation can mark each original phase occurrence at most once
when its retained labels are distinct. -/
theorem optionReserved_count_le (f : α → Option β) (R : List β) (xs : List α)
    (hNodup : (xs.filterMap f).Nodup) :
    (xs.filter (optionReserved f R)).length ≤ R.length := by
  classical
  rw [optionReserved_filter_length]
  apply (hNodup.filter (fun p => @decide (p ∈ R) (Classical.propDecidable _))).length_le_of_subset
  intro p hp
  exact @of_decide_eq_true (p ∈ R) (Classical.propDecidable _) (List.mem_filter.mp hp).2

theorem optionReserved_sum_le (f : α → Option β) (R : List β) (xs : List α)
    (hNodup : (xs.filterMap f).Nodup) :
    (xs.map fun x => if optionReserved f R x then (1:ℝ) else 0).sum ≤ (R.length:ℝ) := by
  have hEq := list_filter_sum_eq (optionReserved f R) (fun _ => (1:ℝ)) xs
  simp only [List.map_const',List.sum_replicate,nsmul_eq_mul,mul_one] at hEq
  rw [← hEq]
  exact_mod_cast optionReserved_count_le f R xs hNodup

end
end StrongSilver
