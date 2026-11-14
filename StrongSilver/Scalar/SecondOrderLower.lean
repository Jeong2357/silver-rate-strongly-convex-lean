-- SPDX-License-Identifier: GPL-3.0-only
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

namespace StrongSilver.Scalar.Calculus
open Set
noncomputable section
set_option maxHeartbeats 800000

/-- A second-order lower bound obtained from two actual mean-value inequalities. -/
theorem second_order_lower (f f' f'' : ℝ → ℝ) (κ : ℝ) (hf0 : f 0=0) (hf'0 : f' 0=0)
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt f' (f'' t) t)
    (hlower : ∀ t ∈ Icc (0 : ℝ) 1, κ ≤ f'' t) : κ/2 ≤ f 1 := by
  let G := fun t : ℝ => f' t-κ*t
  have hG (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt G (f'' t-κ) t := by
    convert! (hf' t ht).sub ((hasDerivAt_id t).const_mul κ) using 1 <;> simp [G]
  have hmG : MonotoneOn G (Icc (0 : ℝ) 1) :=
    monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (fun t ht => (hG t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hG t (interior_subset ht)).differentiableAt.differentiableWithinAt)
      (fun t ht => by rw [(hG t (interior_subset ht)).deriv]; exact sub_nonneg.mpr (hlower t (interior_subset ht)))
  have hGpos (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : 0 ≤ G t := by
    have h := hmG (a := 0) (b := t) (by constructor <;> norm_num) ht ht.1
    simpa only [G,hf'0,mul_zero,sub_zero] using h
  let H := fun t : ℝ => f t-κ/2*t^2
  have hH (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt H (G t) t := by
    convert! (hf t ht).sub (((hasDerivAt_id t).pow 2).const_mul (κ/2)) using 1 <;> simp only [G,pow_one,mul_one,id_eq] <;> ring
  have hmH : MonotoneOn H (Icc (0 : ℝ) 1) :=
    monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (fun t ht => (hH t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hH t (interior_subset ht)).differentiableAt.differentiableWithinAt)
      (fun t ht => by rw [(hH t (interior_subset ht)).deriv]; exact hGpos t (interior_subset ht))
  have hfinal := hmH (a := 0) (b := 1) (by constructor <;> norm_num) (by constructor <;> norm_num) (by norm_num)
  dsimp [H] at hfinal
  rw [hf0] at hfinal
  norm_num at hfinal
  linarith

end
end StrongSilver.Scalar.Calculus
