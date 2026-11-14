-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.AdjacentAvailability

namespace StrongSilver
noncomputable section
variable {α : Type*}
set_option maxHeartbeats 4800000

/-- Removing reserved endpoints excludes at most two adjacent
occurrences for each reserved entry, even after any earlier filtering. -/
theorem adjacent_reserved_loss (reserved : α → Bool) (xs : List α) (pairs : List (α × α))
    (hPairs : pairs.Sublist (adjacentOccurrences xs)) :
    (pairs.length:ℝ) ≤ ((pairs.filter fun p => !reserved p.1 && !reserved p.2).length:ℝ)+
      2*(xs.map fun x => if reserved x then (1:ℝ) else 0).sum := by
  have hPoint (p : α × α) : (1:ℝ) ≤ (if !reserved p.1 && !reserved p.2 then 1 else 0)+
      (if reserved p.1 then (1:ℝ) else 0)+(if reserved p.2 then (1:ℝ) else 0) := by
    cases h1 : reserved p.1 <;> cases h2 : reserved p.2 <;> norm_num [h1,h2]
  have hSum := List.sum_le_sum (fun p (_ : p ∈ pairs) => hPoint p)
  simp only [List.sum_map_add,List.map_const',List.sum_replicate,nsmul_eq_mul,mul_one] at hSum
  have hFiltered : ((pairs.filter fun p => !reserved p.1 && !reserved p.2).length:ℝ) =
      (pairs.map fun p => if !reserved p.1 && !reserved p.2 then (1:ℝ) else 0).sum := by
    simpa only [List.map_const',List.sum_replicate,nsmul_eq_mul,mul_one] using
      list_filter_sum_eq (fun p => !reserved p.1 && !reserved p.2) (fun _ => 1) pairs
  rw [← hFiltered] at hSum
  let F := fun x : α => if reserved x then (1:ℝ) else 0
  have hF (x : α) : 0 ≤ F x := by dsimp only [F]; split_ifs <;> norm_num
  have hFirst := (hPairs.map (fun p => F p.1)).sum_le_sum (by
    intro x hx
    obtain ⟨p,_,rfl⟩ := List.mem_map.mp hx
    exact hF p.1)
  have hSecond := (hPairs.map (fun p => F p.2)).sum_le_sum (by
    intro x hx
    obtain ⟨p,_,rfl⟩ := List.mem_map.mp hx
    exact hF p.2)
  have hFirstAll := adjacentOccurrences_fst_sum_le F hF xs
  have hSecondAll := adjacentOccurrences_snd_sum_le F hF xs
  dsimp only [F] at hFirst hSecond hFirstAll hSecondAll
  linear_combination hSum+hFirst+hSecond+hFirstAll+hSecondAll

end
end StrongSilver
