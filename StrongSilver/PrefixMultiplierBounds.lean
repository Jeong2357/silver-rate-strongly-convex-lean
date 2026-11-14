-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ScalarRampSuffix
import StrongSilver.Transform

namespace StrongSilver
open Real
noncomputable section
set_option maxHeartbeats 1000000

theorem quadraticMultiplier_le_negativeProduct {μ : ℝ} (hμ : 0 ≤ μ) (h : List ℝ)
    (hh : ∀ b ∈ h, μ*b < 1) : quadraticMultiplier μ h ≤ scalarNegativeProduct μ h := by
  induction h with
  | nil => exact le_rfl
  | cons b h ih =>
    have ht := fun c hc => hh c (List.mem_cons_of_mem b hc)
    have htail := ih ht
    have hq := (quadraticMultiplier_positive h ht).le
    have hf : 1-μ*b ≤ scalarNegativeFactor μ b := by
      have hm := mul_le_mul_of_nonneg_left (le_max_left (-b) 0) hμ
      unfold scalarNegativeFactor
      nlinarith only [hm]
    have hn : 0 ≤ scalarNegativeFactor μ b :=
      add_nonneg zero_le_one (mul_nonneg hμ (le_max_right _ _))
    exact mul_le_mul hf htail hq hn

theorem scalarNegativeProduct_mono {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (h : List ℝ) :
    scalarNegativeProduct s h ≤ scalarNegativeProduct t h := by
  induction h with
  | nil => exact le_rfl
  | cons b h ih =>
    have hf : scalarNegativeFactor s b ≤ scalarNegativeFactor t b :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right hst (le_max_right _ _))
    have htail : 0 ≤ scalarNegativeProduct s h := by
      apply List.prod_nonneg
      intro v hv
      obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hv
      exact add_nonneg zero_le_one (mul_nonneg hs (le_max_right _ _))
    have hn : 0 ≤ scalarNegativeFactor t b :=
      add_nonneg zero_le_one (mul_nonneg (hs.trans hst) (le_max_right _ _))
    exact mul_le_mul hf ih htail hn

theorem negativeLogSum_take_le {T : ℝ} (hT : 0 < T) (h : List ℝ) (i : ℕ) :
    negativeLogSum (h.take i) T ≤ negativeLogSum h T := by
  have hh : negativeLogSum h T = negativeLogSum (h.take i) T+negativeLogSum (h.drop i) T := by
    conv_lhs => rw [← List.take_append_drop i h]
    simp only [negativeLogSum,List.map_append,List.sum_append]
  linarith only [hh,negativeLogSum_nonnegative hT (h.drop i)]

theorem prefixMultiplier_le_negative_exp {μ T : ℝ} (hμ : 0 ≤ μ) (hT : 0 < T) (hμT : μ ≤ 1/T)
    (h : List ℝ) (hh : ∀ b ∈ h, μ*b < 1) (i : ℕ) :
    quadraticMultiplier μ (h.take i) ≤ Real.exp (negativeLogSum h T) := by
  have hq := quadraticMultiplier_le_negativeProduct hμ (h.take i) (fun b hb => hh b (List.mem_of_mem_take hb))
  have hm := scalarNegativeProduct_mono hμ hμT (h.take i)
  rw [scalarNegativeProduct_eq_exp hT] at hm
  exact hq.trans (hm.trans (Real.exp_le_exp.mpr (negativeLogSum_take_le hT h i)))

end
end StrongSilver
