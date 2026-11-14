-- SPDX-License-Identifier: GPL-3.0-only
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace StrongSilver
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 2600000

/-- Exact finite partition by a natural-number height bin, retaining
every occurrence of the original list. -/
theorem list_sum_by_nat_bins {α : Type*} (xs : List α) (key : α → ℕ) (f : α → ℝ) (N : ℕ)
    (hkey : ∀ x ∈ xs, key x < N) :
    (∑ j ∈ Finset.range N, ((xs.filter fun x => decide (key x = j)).map f).sum) = (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := hkey x (by simp)
    have hi := ih (fun y hy => hkey y (List.mem_cons_of_mem x hy))
    have hcons (j : ℕ) : (((x::xs).filter fun y => decide (key y = j)).map f).sum =
        (if key x = j then f x else 0)+((xs.filter fun y => decide (key y = j)).map f).sum := by
      by_cases he : key x = j
      · simp only [List.filter_cons,he,decide_true,↓reduceIte,List.map_cons,List.sum_cons]
      · simp only [List.filter_cons,he,decide_false,Bool.false_eq_true,↓reduceIte,zero_add]
    simp_rw [hcons]
    rw [Finset.sum_add_distrib,hi]
    have hhead : (∑ j ∈ Finset.range N, if key x = j then f x else 0) = f x := by
      rw [Finset.sum_eq_single (key x)]
      · exact if_pos rfl
      · intro j hj hne
        exact if_neg (Ne.symm hne)
      · intro hn
        exact False.elim (hn (Finset.mem_range.mpr hx))
    rw [hhead]
    rfl

end
end StrongSilver
