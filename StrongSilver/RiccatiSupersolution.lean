-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.RiccatiBarrier
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace StrongSilver
open Set
open scoped NNReal
noncomputable section

theorem continuousOn_nn_abs_bound {a b : ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b)) :
    ∃ M : ℝ≥0, ∀ t ∈ Icc a b, |f t| ≤ M := by
  obtain ⟨M,hM⟩ := (isCompact_Icc : IsCompact (Icc a b)).exists_bound_of_continuousOn hf
  refine ⟨⟨max M 0,le_max_right _ _⟩,fun t ht => ?_⟩
  have hh : |f t| ≤ M := by simpa only [Real.norm_eq_abs] using hM t ht
  exact hh.trans (le_max_left _ _)

theorem exists_Riccati_below_supersolution {a b : ℝ} (hab : a ≤ b) (r α β U U' : ℝ → ℝ)
    (hrc : ContinuousOn r (Icc a b)) (hαc : ContinuousOn α (Icc a b))
    (hβc : ContinuousOn β (Icc a b))
    (hU : ∀ t ∈ Icc a b, HasDerivWithinAt U (U' t) (Icc a b) t)
    (hUb : ∀ t ∈ Icc a b, 0 ≤ U t) (hr : ∀ t ∈ Ico a b, 0 < r t)
    (hstrict : ∀ t ∈ Ico a b, r t+α t*U t+β t*(U t)^2 < U' t) :
    ∃ J : ℝ → ℝ, J a = 0 ∧ ∀ t ∈ Icc a b,
      0 ≤ J t ∧ J t ≤ U t ∧ HasDerivWithinAt J (r t+α t*J t+β t*(J t)^2) (Icc a b) t := by
  obtain ⟨R,hrb⟩ := continuousOn_nn_abs_bound hrc
  obtain ⟨A,hαb⟩ := continuousOn_nn_abs_bound hαc
  obtain ⟨B,hβb⟩ := continuousOn_nn_abs_bound hβc
  obtain ⟨L,hUb'⟩ := continuousOn_nn_abs_bound (fun t ht => (hU t ht).continuousWithinAt)
  exact exists_Riccati_of_supersolution hab r α β U U' L R A B hrc hαc hβc hrb hαb hβb
    hU (fun t ht => ⟨hUb t ht,(le_abs_self _).trans (hUb' t ht)⟩) hr hstrict

def riccatiUpper (a c δ : ℝ) (J₀ : ℝ → ℝ) (t : ℝ) : ℝ := c*Real.exp (δ*(t-a))*J₀ t

theorem riccatiUpper_hasDerivWithinAt {a c δ t : ℝ} {s : Set ℝ} {J₀ : ℝ → ℝ} {r α₀ : ℝ}
    (hJ₀ : HasDerivWithinAt J₀ (r+α₀*J₀ t) s t) :
    HasDerivWithinAt (riccatiUpper a c δ J₀)
      (c*Real.exp (δ*(t-a))*(r+(α₀+δ)*J₀ t)) s t := by
  have hd := (((hasDerivWithinAt_id t s).sub_const a).const_mul δ).exp
  have hh := (hd.const_mul c).mul hJ₀
  convert! hh using 1 <;> simp only [riccatiUpper,Pi.mul_apply,id_eq] <;> ring

theorem riccatiUpper_strict {a c δ t r α₀ α β : ℝ} {J₀ : ℝ → ℝ}
    (hc : 1 < c) (hδ : 0 ≤ δ) (ht : a ≤ t) (hr : 0 < r) (hJ : 0 ≤ J₀ t)
    (hperturb : α-α₀+β*riccatiUpper a c δ J₀ t ≤ δ) :
    r+α*riccatiUpper a c δ J₀ t+β*(riccatiUpper a c δ J₀ t)^2 <
      c*Real.exp (δ*(t-a))*(r+(α₀+δ)*J₀ t) := by
  have he : 1 ≤ Real.exp (δ*(t-a)) := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (mul_nonneg hδ (sub_nonneg.mpr ht))
  have hcoef : 1 < c*Real.exp (δ*(t-a)) :=
    hc.trans_le (le_mul_of_one_le_right (by linarith : 0 ≤ c) he)
  have hU : 0 ≤ riccatiUpper a c δ J₀ t := mul_nonneg (by linarith) hJ
  have hp := mul_le_mul_of_nonneg_right hperturb hU
  have hstrict := mul_lt_mul_of_pos_right hcoef hr
  unfold riccatiUpper at *
  nlinarith only [hp,hstrict]

end
end StrongSilver
