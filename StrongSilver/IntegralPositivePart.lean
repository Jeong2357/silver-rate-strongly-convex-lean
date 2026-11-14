-- SPDX-License-Identifier: GPL-3.0-only
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace StrongSilver
open MeasureTheory Set
noncomputable section
set_option maxHeartbeats 2200000

theorem intervalIntegrable_positive_part {f : ℝ → ℝ} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) : IntervalIntegrable (fun y => max (f y) 0) volume a b := by
  have heq : (fun y => max (f y) 0) = fun y => (|f y|+f y)/2 := by
    funext y
    by_cases hy : 0 ≤ f y
    · rw [max_eq_left hy,abs_of_nonneg hy]; ring
    · rw [max_eq_right (le_of_not_ge hy),abs_of_nonpos (le_of_not_ge hy)]; ring
  rw [heq]
  exact (hf.abs.add hf).div_const 2

theorem positive_part_integral_le_of_lower {f : ℝ → ℝ} {a b e : ℝ}
    (hab : a ≤ b) (he : 0 ≤ e) (hf : IntervalIntegrable f volume a b)
    (hlower : ∀ y ∈ Icc a b, -e ≤ f y) :
    (∫ y in a..b, max (f y) 0) ≤ (∫ y in a..b, f y)+e*(b-a) := by
  have hmax := intervalIntegrable_positive_part hf
  have hsum : IntervalIntegrable (fun y => f y+e) volume a b := hf.add intervalIntegrable_const
  have hpoint : ∀ y ∈ Icc a b, max (f y) 0 ≤ f y+e := by
    intro y hy
    exact max_le (by linarith only [he]) (by linarith only [hlower y hy])
  have hi := intervalIntegral.integral_mono_on hab hmax hsum hpoint
  rw [intervalIntegral.integral_add hf intervalIntegrable_const,intervalIntegral.integral_const] at hi
  simpa only [smul_eq_mul,mul_comm e] using hi

end
end StrongSilver
