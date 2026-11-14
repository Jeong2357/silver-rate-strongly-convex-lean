-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.GoodDepthEnvelope

namespace StrongSilver.BinaryForest
open Real Set MeasureTheory
noncomputable section
variable {α : Type*}
set_option maxHeartbeats 6800000

def GoodHeightVisible (G : α → Bool) (H : α → ℝ) (parent : Option α) (x : α) (y : ℝ) : Prop :=
  G x = true ∧ ∃ p, parent = some p ∧ G p = true ∧ H x ≤ y ∧ y < H p

local instance goodVisibleDecidable (G : α → Bool) (H : α → ℝ) (parent : Option α) (x : α) (y : ℝ) :
    Decidable (GoodHeightVisible G H parent x y) := Classical.propDecidable _

def goodVisibleDepthTotal (G : α → Bool) (H F : α → ℝ) (v : ℝ) (j : ℕ)
    (parent : Option α) : BinaryTree α → ℝ → ℝ
  | .nil => fun _ => 0
  | t@(.node x l r) => fun y =>
      (if @GoodHeightVisible α G H parent x y then Real.exp (v*y)*goodDepthSum G F j t else 0)+
      goodVisibleDepthTotal G H F v j (some x) l y+goodVisibleDepthTotal G H F v j (some x) r y

theorem goodHeightVisible_integrable (G : α → Bool) (H : α → ℝ) (v a b : ℝ) (parent : Option α) (x : α) :
    IntervalIntegrable (fun y => if @GoodHeightVisible α G H parent x y then Real.exp (v*y) else 0) volume a b := by
  classical
  cases parent with
  | none =>
    have he : (fun y => if @GoodHeightVisible α G H none x y then Real.exp (v*y) else 0) = fun _ => (0:ℝ) := by
      funext y
      simp [GoodHeightVisible]
    rw [he]
    exact intervalIntegrable_const
  | some p =>
    by_cases hg : G x = true ∧ G p = true
    · have hm : Measurable (fun y => if @GoodHeightVisible α G H (some p) x y then Real.exp (v*y) else 0) := by
        apply Measurable.ite _ ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable) measurable_const
        have hs : {y | @GoodHeightVisible α G H (some p) x y} = Ico (H x) (H p) := by
          ext y
          simp only [GoodHeightVisible,Option.some.injEq,exists_eq_left',hg.1,hg.2,true_and,mem_Ico,mem_setOf_eq]
        rw [hs]
        exact measurableSet_Ico
      have hi : IntervalIntegrable (fun y : ℝ => Real.exp (v*y)) volume a b :=
        (Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable a b
      apply hi.mono_fun' hm.aestronglyMeasurable.restrict
      filter_upwards [] with y
      split_ifs <;> simp only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),norm_zero,abs_zero] <;> first | exact le_rfl | exact (Real.exp_pos _).le
    · have he : (fun y => if @GoodHeightVisible α G H (some p) x y then Real.exp (v*y) else 0) = fun _ => (0:ℝ) := by
        funext y
        apply if_neg
        intro hh
        obtain ⟨hx,q,hq,hqp,_,_⟩ := hh
        have hEq : p = q := Option.some.inj hq
        exact hg ⟨hx,hEq.symm ▸ hqp⟩
      rw [he]
      exact intervalIntegrable_const

theorem goodVisibleDepthTotal_integrable (G : α → Bool) (H F : α → ℝ) (v a b : ℝ)
    (j : ℕ) (parent : Option α) (t : BinaryTree α) :
    IntervalIntegrable (goodVisibleDepthTotal G H F v j parent t) volume a b := by
  classical
  induction t generalizing parent with
  | nil => exact intervalIntegrable_const
  | node x l r il ir =>
    have hroot : IntervalIntegrable (fun y => if @GoodHeightVisible α G H parent x y then
        Real.exp (v*y)*goodDepthSum G F j (.node x l r) else 0) volume a b := by
      have he : (fun y => if @GoodHeightVisible α G H parent x y then
          Real.exp (v*y)*goodDepthSum G F j (.node x l r) else 0) =
          fun y => (if @GoodHeightVisible α G H parent x y then Real.exp (v*y) else 0)*goodDepthSum G F j (.node x l r) := by
        funext y
        split_ifs <;> simp
      rw [he]
      exact (goodHeightVisible_integrable G H v a b parent x).mul_const _
    exact (hroot.add (il (some x))).add (ir (some x))

/-- Each visible root with a good parent is below its own height plus
one controlled edge length. This is the pointwise link to the cutoff
envelope. -/
theorem goodVisibleDepthTotal_le_envelope (G : α → Bool) (H F : α → ℝ) (v ω ε : ℝ)
    (hF : ∀ x, 0 ≤ F x) (j : ℕ) (parent : Option α) (t : BinaryTree α)
    (he : GoodEdgeDeviation G H ω ε t)
    (hparent : ∀ p, parent = some p → G p = true → rootGood G t = true →
      |H p-rootHeight H t-ω| ≤ ε) (y : ℝ) :
    goodVisibleDepthTotal G H F v j parent t y ≤ goodDepthEnvelope G H F v (ω+ε) j t y := by
  classical
  induction t generalizing parent with
  | nil => exact le_rfl
  | node x l r il ir =>
    have hL := il (some x) he.1 (by intro p hp hgp hgl; have hx : x = p := Option.some.inj hp; subst p; exact he.2.2.1 hgp hgl)
    have hR := ir (some x) he.2.1 (by intro p hp hgp hgr; have hx : x = p := Option.some.inj hp; subst p; exact he.2.2.2 hgp hgr)
    have hRoot : (if @GoodHeightVisible α G H parent x y then Real.exp (v*y)*goodDepthSum G F j (.node x l r) else 0) ≤
        (if y < H x+(ω+ε) then Real.exp (v*y) else 0)*goodDepthSum G F j (.node x l r) := by
      by_cases hv : @GoodHeightVisible α G H parent x y
      · have hvis := hv
        obtain ⟨hg,p,hp,hgp,_,hy⟩ := hv
        have hh := (abs_le.mp (hparent p hp hgp hg)).2
        have hupper : y < H x+(ω+ε) := by change H p-H x-ω ≤ ε at hh; linarith only [hh,hy]
        simp only [if_pos hvis,if_pos hupper,le_refl]
      · rw [if_neg hv]
        apply mul_nonneg _ (goodDepthSum_nonnegative G F hF j (.node x l r))
        split_ifs <;> positivity
    simp only [goodVisibleDepthTotal,goodDepthEnvelope]
    linear_combination hRoot+hL+hR

end
end StrongSilver.BinaryForest
