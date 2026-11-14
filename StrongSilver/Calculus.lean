-- SPDX-License-Identifier: GPL-3.0-only
-- Adapted from SilverAudit/WorstCaseBasics.lean, v1.0.0,
-- Yechan Jeong and Youngjoon Hong.
import StrongSilver.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace StrongSilver
open Set
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

theorem quadratic_hasGradientAt (s : ℝ) (x : V) :
    HasGradientAt (fun y : V => (s/2)*‖y‖^2) (s • x) x := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  have he : (s/2) • (2 • innerSL ℝ x)=InnerProductSpace.toDual ℝ V (s • x) := by
    ext y
    simp only [ContinuousLinearMap.smul_apply,InnerProductSpace.toDual_apply_apply,
      innerSL_apply_apply,smul_eq_mul]
    rw [real_inner_smul_left]
    ring
  simpa only [he] using (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (s/2)

theorem quadratic_convex (s : ℝ) (hs : 0 ≤ s) :
    ConvexOn ℝ univ (fun y : V => (s/2)*‖y‖^2) :=
  ((convexOn_norm convex_univ).pow (fun _ _ => norm_nonneg _) 2).smul (by positivity)

theorem quadratic_lipschitz (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) (x y : V) :
    ‖s • x-s • y‖ ≤ ‖x-y‖ := by
  rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_nonneg hs]
  exact mul_le_of_le_one_left (norm_nonneg _) hs1

theorem gradient_zero_at_min (f : V → ℝ) (g : V → V) (x : V)
    (hg : HasGradientAt f (g x) x) (hm : ∀ y, f x ≤ f y) : g x=0 := by
  have hmin : IsLocalMin f x := Filter.Eventually.of_forall hm
  have hd := hmin.hasFDerivAt_eq_zero hg.hasFDerivAt
  apply (InnerProductSpace.toDual ℝ V).injective
  simpa using hd

theorem smooth_upper_at_min (f : V → ℝ) (g : V → V) (x₀ xstar : V)
    (hg : ∀ x, HasGradientAt f (g x) x)
    (hL : ∀ x y, ‖g x-g y‖ ≤ ‖x-y‖) (hm : ∀ x, f xstar ≤ f x) :
    f x₀-f xstar ≤ ‖x₀-xstar‖^2/2 := by
  let v := x₀-xstar
  let line := fun t : ℝ => xstar+t • v
  let F := fun t : ℝ => f (line t)-(‖v‖^2/2)*t^2
  have hzero := gradient_zero_at_min f g xstar (hg xstar) hm
  have hline (t : ℝ) : HasDerivAt line v t := by
    simpa only [line,id_eq,one_smul] using ((hasDerivAt_id t).smul_const v).const_add xstar
  have hf (t : ℝ) : HasDerivAt F (inner ℝ (g (line t)) v-‖v‖^2*t) t := by
    have h := ((hg (line t)).hasFDerivAt.comp_hasDerivAt t (hline t)).sub
      (((hasDerivAt_id t).pow 2).const_mul (‖v‖^2/2))
    convert! h using 1
    simp only [InnerProductSpace.toDual_apply_apply,id_eq,pow_one]
    ring
  have hder (t : ℝ) (ht : t ∈ interior (Icc (0 : ℝ) 1)) : deriv F t ≤ 0 := by
    rw [(hf t).deriv]
    have ht0 : 0 ≤ t := (interior_subset ht).1
    have hl := hL (line t) xstar
    rw [hzero,sub_zero] at hl
    have he : line t-xstar=t • v := by dsimp [line]; abel
    rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht0] at hl
    have hinner := real_inner_le_norm (g (line t)) v
    have hmul := mul_le_mul_of_nonneg_right hl (norm_nonneg v)
    nlinarith
  have hanti := antitoneOn_of_deriv_nonpos (convex_Icc (0 : ℝ) 1)
    (continuous_iff_continuousAt.mpr (fun t => (hf t).continuousAt)).continuousOn
    (fun t _ => (hf t).differentiableAt.differentiableWithinAt) hder
  have h := hanti (by simp : (0 : ℝ) ∈ Icc (0 : ℝ) 1)
    (by simp : (1 : ℝ) ∈ Icc (0 : ℝ) 1) zero_le_one
  dsimp [F,line,v] at h
  simp only [one_smul,zero_smul,add_zero,zero_pow (by decide : 2 ≠ 0),mul_zero,sub_zero,
    one_pow,mul_one,add_sub_cancel] at h
  linarith

end
end StrongSilver
