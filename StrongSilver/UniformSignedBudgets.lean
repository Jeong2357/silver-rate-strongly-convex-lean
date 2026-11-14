-- SPDX-License-Identifier: GPL-3.0-only
import Mathlib.Tactic

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 3000000

/-- Homogeneous finite budget conversion. The common lower scale A/(K*s),
upper exterior scale K*A*t and actual negative mass K*A*n give all three
joining budgets once their dimensionless coefficients are small. -/
theorem uniform_signed_budgets {A K s t n L U N Z c : ℝ}
    (hA : 0 < A) (hK : 0 < K) (hs : 0 < s) (ht : 0 ≤ t) (hn : 0 ≤ n)
    (hU : 0 ≤ U) (hN : 0 ≤ N) (hZ : 0 ≤ Z) (hc : 0 ≤ c)
    (hL : A/(K*s) ≤ L) (hUp : U ≤ K*A*t) (hNp : N ≤ K*A*n)
    (hsmallN : 1000*K^2*s*n ≤ 1)
    (hsmallPair : 2*K^4*s^2*t*n ≤ c)
    (hsmallZ : 2*K^2*s*t*Z ≤ c) :
    N ≤ L/1000 ∧ 2*U*N ≤ c*L^2 ∧ 2*U*Z ≤ c*L := by
  have hD : 0 < K*s := mul_pos hK hs
  have hLm : A ≤ L*(K*s) := (div_le_iff₀ hD).mp hL
  have hLp : 0 < L := (div_pos hA hD).trans_le hL
  have hNbound := mul_le_mul_of_nonneg_left hNp (show 0 ≤ 1000*K*s by positivity)
  have hNsmall := mul_le_mul_of_nonneg_right hsmallN hA.le
  have hNscaled : (1000*N)*(K*s) ≤ L*(K*s) := by
    nlinarith only [hNbound,hNsmall,hLm]
  have hNL : 1000*N ≤ L := (mul_le_mul_iff_left₀ hD).mp hNscaled
  have hUN := mul_le_mul hUp hNp hN (show 0 ≤ K*A*t by positivity)
  have hUNscaled := mul_le_mul_of_nonneg_right hUN (sq_nonneg (K*s))
  have hUNsmall := mul_le_mul_of_nonneg_right hsmallPair (sq_nonneg A)
  have hLsq : A^2 ≤ (L*(K*s))^2 := (sq_le_sq₀ hA.le (mul_pos hLp hD).le).mpr hLm
  have hcL := mul_le_mul_of_nonneg_left hLsq hc
  have hpairscaled : (2*U*N)*(K*s)^2 ≤ (c*L^2)*(K*s)^2 := by
    nlinarith only [hUNscaled,hUNsmall,hcL]
  have hpair := (mul_le_mul_iff_left₀ (sq_pos_of_pos hD)).mp hpairscaled
  have hUZ := mul_le_mul_of_nonneg_right hUp hZ
  have hUZscaled := mul_le_mul_of_nonneg_right hUZ hD.le
  have hUZsmall := mul_le_mul_of_nonneg_right hsmallZ hA.le
  have hcLm := mul_le_mul_of_nonneg_left hLm hc
  have hZscaled : (2*U*Z)*(K*s) ≤ (c*L)*(K*s) := by
    nlinarith only [hUZscaled,hUZsmall,hcLm]
  have hheight := (mul_le_mul_iff_left₀ hD).mp hZscaled
  exact ⟨by linarith only [hNL],hpair,hheight⟩

end
end StrongSilver
