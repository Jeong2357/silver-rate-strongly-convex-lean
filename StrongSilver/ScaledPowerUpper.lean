-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.Constants
import StrongSilver.CutPowerPadding
import Mathlib.Algebra.BigOperators.Ring.List

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 1600000

/-- A scale-dependent linear majorant for the concave power. It gives the
same homogeneous sum bound needed at the averaging cutoffs. -/
theorem scaled_power_upper {x A : ℝ} (hx : 0 ≤ x) (hA : 0 < A) :
    x^nu ≤ A^nu+x*A^(nu-1) := by
  by_cases hxA : x ≤ A
  · have hh := Real.rpow_le_rpow hx hxA nu_positive.le
    have hp := mul_nonneg hx (Real.rpow_pos_of_pos hA (nu-1)).le
    linarith only [hh,hp]
  · have hx0 : 0 < x := hA.trans (lt_of_not_ge hxA)
    have hi : x^(nu-1) ≤ A^(nu-1) :=
      Real.rpow_le_rpow_of_nonpos hA (le_of_not_ge hxA) (by linarith [nu_lt_one])
    have hm := mul_le_mul_of_nonneg_left hi hx
    have he : x*x^(nu-1) = x^nu := by
      calc
        _ = x^(1 : ℝ)*x^(nu-1) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add hx0]; congr 1; ring
    rw [he] at hm
    have hp := (Real.rpow_pos_of_pos hA nu).le
    linarith only [hm,hp]

theorem list_scaled_power_upper {A : ℝ} (hA : 0 < A) (xs : List ℝ) (hx : ∀ x ∈ xs, 0 ≤ x) :
    (xs.map fun x => x^nu).sum ≤ (xs.length : ℝ)*A^nu+xs.sum*A^(nu-1) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hh := scaled_power_upper (hx x (by simp)) hA
    have ht := ih (fun z hz => hx z (List.mem_cons_of_mem x hz))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    nlinarith only [hh,ht]

end
end StrongSilver
