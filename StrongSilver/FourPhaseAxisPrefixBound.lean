-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseTimeChange
import StrongSilver.FourPhaseCoordinates
import StrongSilver.NegativePrefixProduct

namespace StrongSilver.FourPhase
open Scalar.SignedIntervals
noncomputable section
set_option maxHeartbeats 2400000

theorem phase_query_positive_axis {μ T C c a : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hT : 0 < T) (hC : 0 ≤ C) (hc : 0 ≤ c) (ha : 0 ≤ a)
    (ξ g : Coordinates) (hξ : inner ℝ axis ξ ≤ 0) (hg : inner ℝ axis g = a) :
    max (inner ℝ axis (phaseState μ T C ξ g c-(1/T) • g)) 0 ≤
      a*max (c-1) 0/(μ*T) := by
  have hden : 0 < μ*T := mul_pos hμ hT
  have hξpart := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hC hc) hξ
  have hb : (1-μ)*(c-1) ≤ max (c-1) 0 := by
    by_cases hh : 0 ≤ c-1
    · rw [max_eq_left hh]
      nlinarith only [mul_nonneg hμ.le hh]
    · rw [max_eq_right (le_of_not_ge hh)]
      exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hμ1) (le_of_not_ge hh)
  have hp := mul_le_mul_of_nonneg_left hb (div_nonneg ha hden.le)
  have hsub := div_nonneg ha hT.le
  have hright : 0 ≤ a*max (c-1) 0/(μ*T) := div_nonneg (mul_nonneg ha (le_max_right _ _)) hden.le
  apply max_le _ hright
  simp only [phaseState,inner_sub_right,real_inner_smul_right,hg]
  simp only [div_eq_mul_inv] at hp hsub ⊢
  nlinarith only [hξpart,hp,hsub]

/-- The old-space excursion of every query in the first three phases is
controlled by its original negative-step mass. -/
theorem phase_prefix_axis_mass_bound {μ T C a : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hT : 0 < T) (hC : 0 ≤ C) (ha : 0 ≤ a)
    (ξ g : Coordinates) (hξ : inner ℝ axis ξ ≤ 0) (hg : inner ℝ axis g = a)
    (h : List ℝ) (hh : ∀ b ∈ h, μ*b < 1) (hsmall : μ*negativeMass h ≤ 1) (k : ℕ) :
    max (inner ℝ axis (phaseState μ T C ξ g (quadraticMultiplier μ (h.take k))-(1/T) • g)) 0 ≤
      2*a*negativeMass h/T := by
  have hc : 0 ≤ quadraticMultiplier μ (h.take k) :=
    (quadraticMultiplier_positive _ (fun b hb => hh b (List.mem_of_mem_take hb))).le
  have hgeom := phase_query_positive_axis hμ hμ1 hT hC hc ha ξ g hξ hg
  have hexcess := prefix_product_excess_bound hμ.le h hh hsmall k
  have hp := mul_le_mul_of_nonneg_left hexcess (div_nonneg ha (mul_pos hμ hT).le)
  have he : (a/(μ*T))*(2*μ*negativeMass h) = 2*a*negativeMass h/T := by
    field_simp
    <;> ring
  have hl : (a/(μ*T))*max (quadraticMultiplier μ (h.take k)-1) 0 =
      a*max (quadraticMultiplier μ (h.take k)-1) 0/(μ*T) := by ring
  rw [he,hl] at hp
  exact hgeom.trans hp

end
end StrongSilver.FourPhase
