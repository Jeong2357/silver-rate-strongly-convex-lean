-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PowerLogFloor

namespace StrongSilver
open Real
noncomputable section
set_option maxHeartbeats 1400000

theorem log_ratio_sum {b : ℝ} (hb : 0 < b) (xs : List ℝ) (hx : ∀ x ∈ xs, 0 < x) :
    (xs.map fun x => Real.log (x/b)).sum = (xs.map Real.log).sum-(xs.length : ℝ)*Real.log b := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have ht := ih (fun z hz => hx z (List.mem_cons_of_mem x hz))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one,
      Real.log_div (hx x (by simp)).ne' hb.ne']
    linarith only [ht]

theorem log_sum_lower_by_reference {b : ℝ} (hb : 0 < b) (ys : List ℝ) (hy : ∀ y ∈ ys, b ≤ y) :
    (ys.length : ℝ)*Real.log b ≤ (ys.map Real.log).sum := by
  induction ys with
  | nil => simp
  | cons y ys ih =>
    have hh := Real.log_le_log hb (hy y (by simp))
    have ht := ih (fun z hz => hy z (List.mem_cons_of_mem y hz))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    nlinarith only [hh,ht]

theorem product_log_le_normalized_sum {b : ℝ} (hb : 0 < b) (xs ys : List ℝ)
    (hx : ∀ x ∈ xs, 0 < x) (hy : ∀ y ∈ ys, b ≤ y) (hlen : xs.length = ys.length) :
    (xs.map Real.log).sum-(ys.map Real.log).sum ≤ (xs.map fun x => Real.log (x/b)).sum := by
  rw [log_ratio_sum hb xs hx,hlen]
  have hh := log_sum_lower_by_reference hb ys hy
  linarith only [hh]

/-- The initial product denominator supplies one reference scale per gap
factor, including the separate terminal denominator when it is present. -/
theorem product_power_reserve {b : ℝ} (hb : 0 < b) (xs ys : List ℝ)
    (hx : ∀ x ∈ xs, 0 < x) (hy : ∀ y ∈ ys, b ≤ y) (hlen : xs.length = ys.length) :
    (xs.length : ℝ)*powerLogMinimum*b^nu ≤
      (xs.map fun x => x^nu).sum-splitCoefficient*b^nu*((xs.map Real.log).sum-(ys.map Real.log).sum) :=
  initial_power_log_reserve hb xs hx (product_log_le_normalized_sum hb xs ys hx hy hlen)

end
end StrongSilver
