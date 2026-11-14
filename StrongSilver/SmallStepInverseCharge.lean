-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BackwardPrefixNorm
import StrongSilver.Scalar.SignedIntervals

namespace StrongSilver
open Real
noncomputable section
set_option maxHeartbeats 1000000

theorem inverseLogKernel_one_sub_small {t : ℝ} (ht : t ≤ 1/2) :
    inverseLogKernel (1-t) ≤ 2*max t 0 := by
  rw [inverseLogKernel_eq]
  by_cases ht0 : t ≤ 0
  · rw [max_eq_right ht0]
    have hh : 0 ≤ Real.log (1-t) := Real.log_nonneg (by linarith only [ht0])
    exact max_le (by norm_num) (by linarith only [hh])
  · have htpos : 0 < t := lt_of_not_ge ht0
    have hq : 0 < 1-t := by linarith only [ht]
    have hh := Real.log_le_sub_one_of_pos (inv_pos.mpr hq)
    rw [Real.log_inv] at hh
    have he : (1-t)⁻¹-1 = t/(1-t) := by field_simp [hq.ne']; ring
    rw [he] at hh
    have hratio : t/(1-t) ≤ 2*t := by
      apply (div_le_iff₀ hq).mpr
      nlinarith only [ht,htpos]
    rw [max_eq_left htpos.le]
    exact max_le (by positivity) (hh.trans hratio)

theorem inverseCharge_small_steps {μ A : ℝ} (hμ : 0 ≤ μ) (hcap : μ*A ≤ 1/2)
    (h : List ℝ) (hh : ∀ b ∈ h, 0 < b → b ≤ A) :
    inverseCharge μ h ≤ 2*μ*Scalar.SignedIntervals.positiveMass h := by
  induction h with
  | nil => simp [inverseCharge,Scalar.SignedIntervals.positiveMass]
  | cons b h ih =>
    have ht := ih (fun c hc => hh c (List.mem_cons_of_mem b hc))
    have hb : μ*b ≤ 1/2 := by
      by_cases hb0 : 0 < b
      · exact (mul_le_mul_of_nonneg_left (hh b List.mem_cons_self hb0) hμ).trans hcap
      · have hm := mul_nonpos_of_nonneg_of_nonpos hμ (le_of_not_gt hb0); linarith only [hm]
    have hbK := inverseLogKernel_one_sub_small hb
    have he : max (μ*b) 0 = μ*max b 0 := by
      by_cases hb0 : 0 ≤ b
      · rw [max_eq_left hb0,max_eq_left (mul_nonneg hμ hb0)]
      · rw [max_eq_right (le_of_not_ge hb0),max_eq_right (mul_nonpos_of_nonneg_of_nonpos hμ (le_of_not_ge hb0)),mul_zero]
    rw [he] at hbK
    change inverseLogKernel (1-μ*b)+inverseCharge μ h ≤ 2*μ*(max b 0+Scalar.SignedIntervals.positiveMass h)
    nlinarith only [ht,hbK]

theorem smallPositiveSum_le_positiveMass (μ : ℝ) (h : List ℝ) :
    smallPositiveSum μ h ≤ Scalar.SignedIntervals.positiveMass h := by
  induction h with
  | nil => exact le_rfl
  | cons b h ih =>
    have hb : smallPositiveStep μ b ≤ max b 0 := by
      unfold smallPositiveStep
      split_ifs with hh
      · exact le_max_left _ _
      · exact le_max_right _ _
    exact add_le_add hb ih

end
end StrongSilver
