-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.RiccatiSupersolution

namespace StrongSilver
open Set Real
noncomputable section

/-- A bounded nonnegative linear comparison solution controls a small quadratic
perturbation on the whole compact time interval. -/
theorem exists_Riccati_small_perturbation {a b δ M : ℝ} (hab : a ≤ b) (hδ : 0 ≤ δ) (hM : 0 ≤ M)
    (r α₀ α β J₀ : ℝ → ℝ)
    (hrc : ContinuousOn r (Icc a b)) (hαc : ContinuousOn α (Icc a b)) (hβc : ContinuousOn β (Icc a b))
    (hJ₀ : ∀ t ∈ Icc a b, HasDerivWithinAt J₀ (r t+α₀ t*J₀ t) (Icc a b) t)
    (hJb : ∀ t ∈ Icc a b, 0 ≤ J₀ t ∧ J₀ t ≤ M)
    (hr : ∀ t ∈ Ico a b, 0 < r t) (hβ : ∀ t ∈ Icc a b, 0 ≤ β t)
    (hperturb : ∀ t ∈ Ico a b, α t-α₀ t+2*β t*M ≤ δ)
    (hscale : (5 : ℝ)/4*Real.exp (δ*(b-a)) ≤ 2) :
    ∃ J : ℝ → ℝ, J a = 0 ∧ ∀ t ∈ Icc a b,
      0 ≤ J t ∧ J t ≤ 2*M ∧ HasDerivWithinAt J (r t+α t*J t+β t*(J t)^2) (Icc a b) t := by
  let U := riccatiUpper a (5/4) δ J₀
  let U' := fun t => (5 : ℝ)/4*Real.exp (δ*(t-a))*(r t+(α₀ t+δ)*J₀ t)
  have hU (t : ℝ) (ht : t ∈ Icc a b) : HasDerivWithinAt U (U' t) (Icc a b) t :=
    riccatiUpper_hasDerivWithinAt (hJ₀ t ht)
  have hUb (t : ℝ) (ht : t ∈ Icc a b) : 0 ≤ U t ∧ U t ≤ 2*M := by
    have hcoef : (5 : ℝ)/4*Real.exp (δ*(t-a)) ≤ 2 :=
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith only [mul_le_mul_of_nonneg_left ht.2 hδ]))
        (by norm_num : (0 : ℝ) ≤ 5/4)).trans hscale
    have hcoef0 : 0 ≤ (5 : ℝ)/4*Real.exp (δ*(t-a)) := by positivity
    exact ⟨mul_nonneg hcoef0 (hJb t ht).1,
      mul_le_mul hcoef (hJb t ht).2 (hJb t ht).1 (by norm_num : (0 : ℝ) ≤ 2)⟩
  have hstrict (t : ℝ) (ht : t ∈ Ico a b) : r t+α t*U t+β t*(U t)^2 < U' t := by
    apply riccatiUpper_strict (by norm_num : (1 : ℝ) < 5/4) hδ ht.1 (hr t ht) (hJb t (Ico_subset_Icc_self ht)).1
    have hp := mul_le_mul_of_nonneg_left (hUb t (Ico_subset_Icc_self ht)).2 (hβ t (Ico_subset_Icc_self ht))
    nlinarith only [hp,hperturb t ht]
  obtain ⟨J,hJ0,hJ⟩ := exists_Riccati_below_supersolution hab r α β U U' hrc hαc hβc hU
    (fun t ht => (hUb t ht).1) hr hstrict
  exact ⟨J,hJ0,fun t ht => ⟨(hJ t ht).1,(hJ t ht).2.1.trans (hUb t ht).2,(hJ t ht).2.2⟩⟩

end
end StrongSilver
