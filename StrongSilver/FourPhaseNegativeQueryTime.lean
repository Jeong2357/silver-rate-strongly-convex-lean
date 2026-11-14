-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseTimeChange
import StrongSilver.NegativePrefixProduct

namespace StrongSilver.FourPhase
open Scalar.SignedIntervals
noncomputable section
set_option maxHeartbeats 2000000

theorem negative_queryTime_bound {μ T C c : ℝ} (hμ : 0 < μ) (hT : 0 < T)
    (hC : 0 < C) (hc : 0 < c) (hCc : 1/2 ≤ C*c) :
    -queryTime μ T C c ≤ 2*max (c-1) 0/(μ*T) := by
  have hden := mul_pos hμ hT
  have he : (-queryTime μ T C c)*(μ*T)*(C*c) = c-1-μ*c := by
    unfold queryTime
    field_simp
    <;> ring
  have hright : 0 ≤ 2*max (c-1) 0/(μ*T) := div_nonneg
    (mul_nonneg (by norm_num) (le_max_right _ _)) hden.le
  by_cases hf : 0 ≤ -queryTime μ T C c
  · have hp := mul_le_mul_of_nonneg_left hCc (mul_nonneg hf hden.le)
    have hm := mul_nonneg hμ.le hc.le
    have hx := le_max_left (c-1) 0
    apply (le_div_iff₀ hden).mpr
    nlinarith only [he,hp,hm,hx]
  · exact (le_of_not_ge hf).trans hright

theorem negative_queryTime_prefix_mass {μ T C : ℝ} (hμ : 0 < μ) (hT : 0 < T) (hC : 0 < C)
    (h : List ℝ) (hh : ∀ b ∈ h, μ*b < 1) (hsmall : μ*negativeMass h ≤ 1) (k : ℕ)
    (hCc : 1/2 ≤ C*quadraticMultiplier μ (h.take k)) :
    -queryTime μ T C (quadraticMultiplier μ (h.take k)) ≤ 4*negativeMass h/T := by
  have hc := quadraticMultiplier_positive (h.take k) (fun b hb => hh b (List.mem_of_mem_take hb))
  have htime := negative_queryTime_bound hμ hT hC hc hCc
  have he := prefix_product_excess_bound hμ.le h hh hsmall k
  have hp := mul_le_mul_of_nonneg_left he (div_nonneg (by norm_num : (0:ℝ) ≤ 2) (mul_pos hμ hT).le)
  have hr : (2/(μ*T))*(2*μ*negativeMass h) = 4*negativeMass h/T := by
    field_simp
    <;> ring
  have hl : (2/(μ*T))*max (quadraticMultiplier μ (h.take k)-1) 0 =
      2*max (quadraticMultiplier μ (h.take k)-1) 0/(μ*T) := by ring
  rw [hr,hl] at hp
  exact htime.trans hp

end
end StrongSilver.FourPhase
