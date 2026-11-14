-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.WeightedTelescoping
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace StrongSilver
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2400000

/-- A finite telescoping majorant for the inverse-cubic log ladder. -/
theorem inverse_cube_step {a s : ℝ} (ha : 0 < a) (hs : 0 < s) :
    1/(a+s)^3 ≤ (1/a^2-1/(a+s)^2)/(2*s) := by
  have hb : 0 < a+s := add_pos ha hs
  have hid : 1/a^2-1/(a+s)^2-2*s/(a+s)^3 = s^2*(3*a+s)/(a^2*(a+s)^3) := by
    field_simp [ha.ne',hb.ne'] <;> ring
  have hn : 0 ≤ s^2*(3*a+s)/(a^2*(a+s)^3) := by positivity
  apply (le_div_iff₀ (mul_pos (by norm_num) hs)).mpr
  rw [← hid] at hn
  linear_combination hn

theorem inverse_cube_ladder_sum {x s : ℝ} (hx : 0 < x) (hs : 0 < s) (n : ℕ) :
    (∑ j ∈ Finset.range n, 1/(x+((j:ℝ)+1)*s)^3) ≤ 1/(2*s*x^2) := by
  have hp : ∀ j : ℕ, 0 < x+(j:ℝ)*s := by
    intro j
    exact add_pos_of_pos_of_nonneg hx (mul_nonneg (Nat.cast_nonneg _) hs.le)
  have hstep : ∀ j < n, 1/(x+((j:ℝ)+1)*s)^3 ≤
      (1/(x+(j:ℝ)*s)^2-1/(x+((j+1:ℕ):ℝ)*s)^2)/(2*s) := by
    intro j hj
    have hh := inverse_cube_step (hp j) hs
    simpa only [Nat.cast_add,Nat.cast_one,add_mul,one_mul,add_assoc] using hh
  have hsum := Finset.sum_le_sum (s := Finset.range n) (fun j hj => hstep j (Finset.mem_range.mp hj))
  rw [← Finset.sum_div,sum_successive_differences] at hsum
  simp only [Nat.cast_zero,zero_mul,add_zero] at hsum
  have hn : 0 ≤ 1/(x+(n:ℝ)*s)^2 := by positivity
  have hb : (1/x^2-1/(x+(n:ℝ)*s)^2)/(2*s) ≤ 1/(2*s*x^2) := by
    have hh := div_le_div_of_nonneg_right (show 1/x^2-1/(x+(n:ℝ)*s)^2 ≤ 1/x^2 by linarith only [hn])
      (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hs.le)
    have heq : (1/x^2)/(2*s) = 1/(2*s*x^2) := by ring
    rwa [heq] at hh
  exact hsum.trans hb

end
end StrongSilver
