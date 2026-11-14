-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.WeightedGoodDepth
import StrongSilver.ExponentialStepIntegral

namespace StrongSilver.BinaryForest
open Real Set MeasureTheory
noncomputable section
variable {α : Type*}
set_option maxHeartbeats 6200000

/-- An integrable envelope for visible good-root depth sums. Each root
contributes only below its height plus one controlled edge length. -/
def goodDepthEnvelope (G : α → Bool) (H F : α → ℝ) (v L : ℝ) (j : ℕ) : BinaryTree α → ℝ → ℝ
  | .nil => fun _ => 0
  | t@(.node x l r) => fun y =>
      (if y < H x+L then Real.exp (v*y) else 0)*goodDepthSum G F j t+
      goodDepthEnvelope G H F v L j l y+goodDepthEnvelope G H F v L j r y

theorem goodDepthEnvelope_integrable (G : α → Bool) (H F : α → ℝ) (v L a b : ℝ)
    (j : ℕ) (t : BinaryTree α) : IntervalIntegrable (goodDepthEnvelope G H F v L j t) volume a b := by
  induction t with
  | nil => exact intervalIntegrable_const
  | node x l r il ir =>
    exact (((exponential_step_intervalIntegrable v (H x+L) a b).mul_const (goodDepthSum G F j (.node x l r))).add il).add ir

theorem exponential_step_scaled_upper (v c a b : ℝ) (hv : 0 ≤ v) (hab : a ≤ b) :
    v*(∫ y in a..b, if y < c then Real.exp (v*y) else 0) ≤ Real.exp (v*c) := by
  rw [exponential_step_integral v a b c hab]
  have hh := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (min_le_right b c) hv)
  linarith only [hh,Real.exp_pos (v*min a c)]

/-- The cutoff integral is paid by the original root weights before
using the unique-ancestor and good-path spacing estimates. -/
theorem goodDepthEnvelope_integral_upper (G : α → Bool) (H F : α → ℝ) (v L a b : ℝ)
    (hv : 0 ≤ v) (hF : ∀ x, 0 ≤ F x) (hab : a ≤ b) (j : ℕ) (t : BinaryTree α) :
    v*(∫ y in a..b, goodDepthEnvelope G H F v L j t y) ≤
      Real.exp (v*L)*weightedGoodDepthTotal G H F v j t := by
  induction t with
  | nil => simp [goodDepthEnvelope,weightedGoodDepthTotal]
  | node x l r il ir =>
    have hs := mul_le_mul_of_nonneg_right (exponential_step_scaled_upper v (H x+L) a b hv hab)
      (goodDepthSum_nonnegative G F hF j (.node x l r))
    have hInt : (∫ y in a..b, goodDepthEnvelope G H F v L j (.node x l r) y) =
        (∫ y in a..b, (if y < H x+L then Real.exp (v*y) else 0)*goodDepthSum G F j (.node x l r))+
        (∫ y in a..b, goodDepthEnvelope G H F v L j l y)+
        (∫ y in a..b, goodDepthEnvelope G H F v L j r y) := by
      rw [goodDepthEnvelope,intervalIntegral.integral_add
        (((exponential_step_intervalIntegrable v (H x+L) a b).mul_const _).add
          (goodDepthEnvelope_integrable G H F v L a b j l))
        (goodDepthEnvelope_integrable G H F v L a b j r),
        intervalIntegral.integral_add ((exponential_step_intervalIntegrable v (H x+L) a b).mul_const _)
          (goodDepthEnvelope_integrable G H F v L a b j l)]
    rw [hInt,intervalIntegral.integral_mul_const]
    rw [mul_add,Real.exp_add] at hs
    simp only [weightedGoodDepthTotal]
    linear_combination hs+il+ir

theorem goodDepthEnvelope_nonnegative (G : α → Bool) (H F : α → ℝ) (v L : ℝ)
    (hF : ∀ x, 0 ≤ F x) (j : ℕ) (t : BinaryTree α) (y : ℝ) :
    0 ≤ goodDepthEnvelope G H F v L j t y := by
  induction t with
  | nil => exact le_rfl
  | node x l r il ir =>
    apply add_nonneg (add_nonneg ?_ il) ir
    apply mul_nonneg _ (goodDepthSum_nonnegative G F hF j (.node x l r))
    split_ifs <;> positivity

end
end StrongSilver.BinaryForest
