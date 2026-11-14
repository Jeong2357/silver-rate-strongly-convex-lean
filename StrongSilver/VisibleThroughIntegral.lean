-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.IncompleteVisibleTree

namespace StrongSilver.BinaryForest
open Real Set MeasureTheory
noncomputable section
variable {α : Type*}
set_option maxHeartbeats 4400000

/-- Finite geometric summation of the cutoff depth bounds. -/
theorem goodVisibleThroughTotal_integral_upper (G : α → Bool) (H F : α → ℝ)
    (v a b C S : ℝ) (parent : Option α) (t : BinaryTree α) (n : ℕ)
    (hb : ∀ k : ℕ, k < n →
      (∫ y in a..b, goodVisibleDepthTotal G H F v k parent t y) ≤ C*(2:ℝ)^k*S) :
    (∫ y in a..b, goodVisibleThroughTotal G H F v parent t n y) ≤ C*((2:ℝ)^n-1)*S := by
  induction n with
  | zero => simp [goodVisibleThroughTotal]
  | succ n ih =>
    have hPrev := ih (fun k hk => hb k (Nat.lt_succ_of_lt hk))
    have hLast := hb n (Nat.lt_succ_self n)
    rw [goodVisibleThroughTotal,intervalIntegral.integral_add
      (goodVisibleDepthTotal_integrable G H F v a b n parent t)
      (goodVisibleThroughTotal_integrable G H F v a b parent t n),pow_succ]
    linear_combination hPrev+hLast

end
end StrongSilver.BinaryForest
