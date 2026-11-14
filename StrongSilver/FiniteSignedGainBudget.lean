-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.Constants
import Mathlib.Algebra.BigOperators.Ring.List

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 3200000

/-- A finite conversion from positive logarithmic gain and power
endpoint bounds to absolute gain and absolute power-change bounds. -/
theorem finite_absolute_gain_budget {α : Type*} (xs : List α) (w g E Δ : α → ℝ)
    (M N K : ℝ) (hw : ∀ x ∈ xs, 0 ≤ w x) (hE : ∀ x ∈ xs, 0 ≤ E x)
    (hΔ : ∀ x ∈ xs, Δ x = splitCoefficient*w x*g x-E x)
    (hpositive : (xs.map fun x => w x*max (g x) 0).sum ≤ M)
    (hpower : -N ≤ (xs.map Δ).sum) (hexcess : (xs.map E).sum ≤ K) :
    (xs.map fun x => w x*|g x|).sum ≤ 2*M+N/splitCoefficient ∧
      (xs.map fun x => |Δ x|).sum ≤ splitCoefficient*(2*M+N/splitCoefficient)+K := by
  have hc := split_coefficient_positive
  have he0 : 0 ≤ (xs.map E).sum := List.sum_nonneg (by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hy
    exact hE x hx)
  have hsum : (xs.map Δ).sum = splitCoefficient*(xs.map fun x => w x*g x).sum-(xs.map E).sum := by
    clear hw hE hpositive hpower hexcess he0
    induction xs with
    | nil => simp
    | cons x xs ih =>
      have hhead := hΔ x (by simp)
      have hi := ih (fun q hq => hΔ q (List.mem_cons_of_mem x hq))
      simp only [List.map_cons,List.sum_cons]
      linear_combination hhead+hi
  have hident : (xs.map fun x => w x*|g x|).sum =
      2*(xs.map fun x => w x*max (g x) 0).sum-(xs.map fun x => w x*g x).sum := by
    clear hw hE hΔ hpositive hpower hexcess he0 hsum
    induction xs with
    | nil => simp
    | cons x xs ih =>
      have he : |g x| = 2*max (g x) 0-g x := by
        by_cases hx : 0 ≤ g x
        · rw [abs_of_nonneg hx,max_eq_left hx]; ring
        · rw [abs_of_nonpos (le_of_not_ge hx),max_eq_right (le_of_not_ge hx)]; ring
      simp only [List.map_cons,List.sum_cons]
      rw [he]
      linear_combination ih
  have hlog : -N/splitCoefficient ≤ (xs.map fun x => w x*g x).sum := by
    apply (div_le_iff₀ hc).mpr
    linarith only [hpower,hsum,he0]
  rw [neg_div] at hlog
  have hAbs : (xs.map fun x => w x*|g x|).sum ≤ 2*M+N/splitCoefficient := by
    rw [hident]
    linarith only [hpositive,hlog]
  refine ⟨hAbs,?_⟩
  have hpoint : ∀ x ∈ xs, |Δ x| ≤ splitCoefficient*(w x*|g x|)+E x := by
    intro x hx
    rw [hΔ x hx]
    have hh := abs_sub_le (splitCoefficient*w x*g x) (0:ℝ) (E x)
    simp only [sub_zero,zero_sub,abs_neg,abs_mul,abs_of_pos hc,abs_of_nonneg (hw x hx),abs_of_nonneg (hE x hx)] at hh
    linear_combination hh
  have hfinal := List.sum_le_sum hpoint
  simp only [List.sum_map_add,List.sum_map_mul_left] at hfinal
  have hh := mul_le_mul_of_nonneg_left hAbs hc.le
  linarith only [hfinal,hh,hexcess]

end
end StrongSilver
