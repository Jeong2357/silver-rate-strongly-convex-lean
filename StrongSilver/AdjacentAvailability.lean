-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FiniteFilteredSums
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

namespace StrongSilver
noncomputable section
variable {α : Type*}
set_option maxHeartbeats 5800000

def adjacentOccurrences : List α → List (α × α)
  | [] => []
  | a::xs => match xs with
    | [] => []
    | b::_ => (a,b)::adjacentOccurrences xs

def unavailableIndicator (good : α → Bool) (x : α) : ℝ := if good x then 0 else 1

def pairAvailable (good deep reserved : α → Bool) (p : α × α) : Bool :=
  good p.1 && good p.2 && deep p.1 && !reserved p.1 && !reserved p.2

theorem unavailableIndicator_nonnegative (good : α → Bool) (x : α) : 0 ≤ unavailableIndicator good x := by
  unfold unavailableIndicator
  split_ifs <;> norm_num

theorem adjacentOccurrences_fst_sublist (xs : List α) : ((adjacentOccurrences xs).map Prod.fst).Sublist xs := by
  induction xs with
  | nil => exact List.Sublist.refl []
  | cons a xs ih =>
    cases xs with
    | nil => simp [adjacentOccurrences]
    | cons b xs => exact ih.cons₂ a

theorem adjacentOccurrences_snd (xs : List α) : ((adjacentOccurrences xs).map Prod.snd) = xs.tail := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases xs with
    | nil => rfl
    | cons b xs => simpa only [adjacentOccurrences,List.map_cons,List.tail_cons] using congrArg (List.cons b) ih

theorem adjacentOccurrences_length (xs : List α) : xs.length ≤ (adjacentOccurrences xs).length+1 := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    cases xs with
    | nil => simp [adjacentOccurrences]
    | cons b xs => simp only [adjacentOccurrences,List.length_cons] at *; omega

theorem adjacentOccurrences_fst_sum_le (F : α → ℝ) (hF : ∀ x, 0 ≤ F x) (xs : List α) :
    ((adjacentOccurrences xs).map fun p => F p.1).sum ≤ (xs.map F).sum := by
  have hh := ((adjacentOccurrences_fst_sublist xs).map F).sum_le_sum (by
    intro x hx
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hx
    exact hF v)
  simpa only [List.map_map,Function.comp_def] using hh

theorem adjacentOccurrences_snd_sum_le (F : α → ℝ) (hF : ∀ x, 0 ≤ F x) (xs : List α) :
    ((adjacentOccurrences xs).map fun p => F p.2).sum ≤ (xs.map F).sum := by
  have hs : ((adjacentOccurrences xs).map Prod.snd).Sublist xs := by
    rw [adjacentOccurrences_snd]
    exact List.tail_sublist xs
  have hh := (hs.map F).sum_le_sum (by
    intro x hx
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hx
    exact hF v)
  simpa only [List.map_map,Function.comp_def] using hh

/-- One failed entry or reservation affects at most two adjacent pairs;
a depth failure affects only the pair that starts at that entry. -/
theorem adjacent_availability_count (good deep reserved : α → Bool) (xs : List α) :
    (xs.length:ℝ) ≤ (((adjacentOccurrences xs).filter (pairAvailable good deep reserved)).length:ℝ)+1+
      2*(xs.map (unavailableIndicator good)).sum+(xs.map (unavailableIndicator deep)).sum+
      2*(xs.map fun x => if reserved x then (1:ℝ) else 0).sum := by
  have hpoint (p : α × α) : (1:ℝ) ≤ (if pairAvailable good deep reserved p then 1 else 0)+
      unavailableIndicator good p.1+unavailableIndicator good p.2+unavailableIndicator deep p.1+
      (if reserved p.1 then (1:ℝ) else 0)+(if reserved p.2 then (1:ℝ) else 0) := by
    cases hga : good p.1 <;> cases hgb : good p.2 <;> cases hda : deep p.1 <;>
      cases hra : reserved p.1 <;> cases hrb : reserved p.2 <;>
      norm_num [pairAvailable,unavailableIndicator,hga,hgb,hda,hra,hrb] <;> positivity
  have hSum := List.sum_le_sum (fun p (_ : p ∈ adjacentOccurrences xs) => hpoint p)
  simp only [List.sum_map_add,List.map_const',List.sum_replicate,nsmul_eq_mul,mul_one] at hSum
  have hAvailable : (((adjacentOccurrences xs).filter (pairAvailable good deep reserved)).length:ℝ) =
      ((adjacentOccurrences xs).map fun p => if pairAvailable good deep reserved p then (1:ℝ) else 0).sum := by
    simpa only [List.map_const',List.sum_replicate,nsmul_eq_mul,mul_one] using
      list_filter_sum_eq (pairAvailable good deep reserved) (fun _ => 1) (adjacentOccurrences xs)
  rw [← hAvailable] at hSum
  have hG1 := adjacentOccurrences_fst_sum_le (unavailableIndicator good) (unavailableIndicator_nonnegative good) xs
  have hG2 := adjacentOccurrences_snd_sum_le (unavailableIndicator good) (unavailableIndicator_nonnegative good) xs
  have hD := adjacentOccurrences_fst_sum_le (unavailableIndicator deep) (unavailableIndicator_nonnegative deep) xs
  have hR (x : α) : 0 ≤ (if reserved x then (1:ℝ) else 0) := by split_ifs <;> norm_num
  have hR1 := adjacentOccurrences_fst_sum_le (fun x => if reserved x then (1:ℝ) else 0) hR xs
  have hR2 := adjacentOccurrences_snd_sum_le (fun x => if reserved x then (1:ℝ) else 0) hR xs
  have hLen : (xs.length:ℝ) ≤ ((adjacentOccurrences xs).length:ℝ)+1 := by exact_mod_cast adjacentOccurrences_length xs
  linear_combination hLen+hSum+hG1+hG2+hD+hR1+hR2

end
end StrongSilver
