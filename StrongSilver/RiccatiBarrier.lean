-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ClippedRiccati
import Mathlib.Analysis.Calculus.MeanValue

namespace StrongSilver
open Set
open scoped NNReal
noncomputable section

theorem clippedRiccati_barriers {a b L : ℝ} {r α β J U U' : ℝ → ℝ}
    (hab : a ≤ b) (hJ0 : J a = 0)
    (hJ : ∀ t ∈ Icc a b, HasDerivWithinAt J (clippedRiccati r α β L t (J t)) (Icc a b) t)
    (hU : ∀ t ∈ Icc a b, HasDerivWithinAt U (U' t) (Icc a b) t)
    (hUb : ∀ t ∈ Icc a b, 0 ≤ U t ∧ U t ≤ L)
    (hr : ∀ t ∈ Ico a b, 0 < r t)
    (hstrict : ∀ t ∈ Ico a b, r t+α t*U t+β t*(U t)^2 < U' t) :
    ∀ t ∈ Icc a b, 0 ≤ J t ∧ J t ≤ U t := by
  have hcJ : ContinuousOn J (Icc a b) := fun t ht => (hJ t ht).continuousWithinAt
  have hcU : ContinuousOn U (Icc a b) := fun t ht => (hU t ht).continuousWithinAt
  have hJright (t : ℝ) (ht : t ∈ Ico a b) :
      HasDerivWithinAt J (clippedRiccati r α β L t (J t)) (Ici t) t :=
    (hJ t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)
  have hUright (t : ℝ) (ht : t ∈ Ico a b) : HasDerivWithinAt U (U' t) (Ici t) t :=
    (hU t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)
  have hupper : ∀ t ∈ Icc a b, J t ≤ U t := by
    apply image_le_of_deriv_right_lt_deriv_boundary' hcJ hJright
      (by rw [hJ0]; exact (hUb a ⟨le_rfl,hab⟩).1) hcU hUright
    intro t ht he
    rw [clippedRiccati,he,clipHeight_eq (hUb t (Ico_subset_Icc_self ht)).1 (hUb t (Ico_subset_Icc_self ht)).2]
    exact hstrict t ht
  have hL : 0 ≤ L := (hUb a ⟨le_rfl,hab⟩).1.trans (hUb a ⟨le_rfl,hab⟩).2
  have hlower : ∀ t ∈ Icc a b, -J t ≤ 0 := by
    apply image_le_of_deriv_right_lt_deriv_boundary' (B := fun _ => 0) (B' := fun _ => 0) hcJ.neg
      (fun t ht => (hJright t ht).neg)
      (by change -J a ≤ 0; rw [hJ0]; norm_num) continuousOn_const
      (fun t ht => hasDerivWithinAt_const t (Ici t) (0 : ℝ))
    intro t ht he
    have hz : J t = 0 := neg_eq_zero.mp he
    simp only [clippedRiccati,hz,clipHeight_eq (le_refl (0 : ℝ)) hL,zero_pow (by decide : 2 ≠ 0),
      mul_zero,add_zero]
    exact neg_neg_of_pos (hr t ht)
  intro t ht
  exact ⟨by linarith [hlower t ht],hupper t ht⟩

/-- An explicit strict supersolution turns the bounded clipped construction into
an actual solution of the original quadratic differential equation. -/
theorem exists_Riccati_of_supersolution {a b : ℝ} (hab : a ≤ b) (r α β U U' : ℝ → ℝ)
    (L R A B : ℝ≥0) (hrc : ContinuousOn r (Icc a b)) (hαc : ContinuousOn α (Icc a b))
    (hβc : ContinuousOn β (Icc a b))
    (hrb : ∀ t ∈ Icc a b, |r t| ≤ R) (hαb : ∀ t ∈ Icc a b, |α t| ≤ A)
    (hβb : ∀ t ∈ Icc a b, |β t| ≤ B)
    (hU : ∀ t ∈ Icc a b, HasDerivWithinAt U (U' t) (Icc a b) t)
    (hUb : ∀ t ∈ Icc a b, 0 ≤ U t ∧ U t ≤ L)
    (hr : ∀ t ∈ Ico a b, 0 < r t)
    (hstrict : ∀ t ∈ Ico a b, r t+α t*U t+β t*(U t)^2 < U' t) :
    ∃ J : ℝ → ℝ, J a = 0 ∧ ∀ t ∈ Icc a b,
      0 ≤ J t ∧ J t ≤ U t ∧ HasDerivWithinAt J (r t+α t*J t+β t*(J t)^2) (Icc a b) t := by
  obtain ⟨J,hJ0,hJ⟩ := exists_clippedRiccati_initial hab r α β L R A B hrc hαc hβc hrb hαb hβb
  have hb := clippedRiccati_barriers hab hJ0 hJ hU hUb hr hstrict
  refine ⟨J,hJ0,fun t ht => ⟨(hb t ht).1,(hb t ht).2,?_⟩⟩
  have hi : clipHeight L (J t) = J t := clipHeight_eq (hb t ht).1 ((hb t ht).2.trans (hUb t ht).2)
  simpa only [clippedRiccati,hi] using hJ t ht

end
end StrongSilver
