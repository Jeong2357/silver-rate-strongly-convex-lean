-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.GoodDepthSpacing
import Mathlib.Analysis.SpecialFunctions.Exp

namespace StrongSilver.BinaryForest
open Real
noncomputable section
variable {α : Type*}
set_option maxHeartbeats 6200000

/-- Sum of depth-j scores weighted by the root height. -/
def weightedGoodDepthTotal (G : α → Bool) (H F : α → ℝ) (v : ℝ) (j : ℕ) : BinaryTree α → ℝ
  | .nil => 0
  | t@(.node x l r) => Real.exp (v*H x)*goodDepthSum G F j t+
      weightedGoodDepthTotal G H F v j l+weightedGoodDepthTotal G H F v j r

theorem weighted_good_depth_root (G : α → Bool) (H F : α → ℝ) (v ω ε : ℝ)
    (hv : 0 ≤ v) (hF : ∀ x, 0 ≤ F x) (j : ℕ) (t : BinaryTree α)
    (he : GoodEdgeDeviation G H ω ε t) :
    Real.exp (v*rootHeight H t)*goodDepthSum G F j t ≤
      Real.exp (v*((j:ℝ)*ω+(j:ℝ)*ε))*goodDepthSum G (fun x => Real.exp (v*H x)*F x) j t := by
  unfold goodDepthSum
  rw [← List.sum_map_mul_left,← List.sum_map_mul_left]
  apply List.sum_le_sum
  intro x hx
  have hheight := (abs_le.mp (goodDepth_height_deviation G H ω ε j t he hx)).2
  have hp : v*rootHeight H t ≤ v*((j:ℝ)*ω+(j:ℝ)*ε)+v*H x := by
    have hs := mul_le_mul_of_nonneg_left hheight hv
    nlinarith only [hs]
  have hexp := Real.exp_le_exp.mpr hp
  rw [Real.exp_add] at hexp
  have hs := mul_le_mul_of_nonneg_right hexp (hF x)
  simpa only [mul_assoc] using hs

/-- A weighted unique-ancestor estimate, prior to the cutoff integral.
The factor depends on depth and the accumulated spacing error. -/
theorem weighted_good_depth_total (G : α → Bool) (H F : α → ℝ) (v ω ε : ℝ)
    (hv : 0 ≤ v) (hF : ∀ x, 0 ≤ F x) (j : ℕ) (t : BinaryTree α)
    (he : GoodEdgeDeviation G H ω ε t) :
    weightedGoodDepthTotal G H F v j t ≤
      Real.exp (v*((j:ℝ)*ω+(j:ℝ)*ε))*
        ((labels t).map fun x => Real.exp (v*H x)*F x).sum := by
  have hmain : weightedGoodDepthTotal G H F v j t ≤
      Real.exp (v*((j:ℝ)*ω+(j:ℝ)*ε))*goodDepthTotal G (fun x => Real.exp (v*H x)*F x) j t := by
    induction t with
    | nil => simp [weightedGoodDepthTotal,goodDepthTotal]
    | node x l r il ir =>
      have hroot := weighted_good_depth_root G H F v ω ε hv hF j (.node x l r) he
      have hL := il he.1
      have hR := ir he.2.1
      change Real.exp (v*H x)*_ ≤ _ at hroot
      simp only [weightedGoodDepthTotal,goodDepthTotal]
      linear_combination hroot+hL+hR
  have hfull := goodDepthTotal_le_labels G (fun x => Real.exp (v*H x)*F x)
    (fun x => mul_nonneg (Real.exp_pos _).le (hF x)) j t
  exact hmain.trans (mul_le_mul_of_nonneg_left hfull (Real.exp_pos _).le)

end
end StrongSilver.BinaryForest
