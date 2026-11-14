-- SPDX-License-Identifier: GPL-3.0-only
import Mathlib.Tactic

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 3000000

/-- A finite common-scale bound for the full group-count error. This
keeps the endpoint gain error separate from all summably small terms. -/
theorem scaled_group_error {A K s t a z g μ M U L N : ℝ}
    (hA : 0 < A) (hK : 0 < K) (hs : 0 < s) (ht : 0 ≤ t)
    (hz : 0 ≤ z) (hg : 0 ≤ g) (hμ : 0 ≤ μ) (hM : 0 ≤ M) (hU : 0 ≤ U)
    (hL : A/(K*s) ≤ L) (hMp : M ≤ K*A) (hUp : U ≤ K*A*t)
    (hcurv : μ*A ≤ a) (hcount : N ≤ s) :
    N*(μ*M+μ*U+g+2*U*z/L) ≤ K*s*a+K*s*t*a+s*g+2*K^2*s^2*t*z := by
  have hD := mul_pos hK hs
  have hLp := (div_pos hA hD).trans_le hL
  have hLm := (div_le_iff₀ hD).mp hL
  have ha : 0 ≤ a := (mul_nonneg hμ hA.le).trans hcurv
  have hM0 := mul_nonneg hμ hM
  have hU0 := mul_nonneg hμ hU
  have hheight0 : 0 ≤ 2*U*z/L := div_nonneg (by positivity) hLp.le
  have hM1 := mul_le_mul_of_nonneg_left hMp hμ
  have hM2 := mul_le_mul_of_nonneg_left hcurv hK.le
  have hMbound : μ*M ≤ K*a := by nlinarith only [hM1,hM2]
  have hU1 := mul_le_mul_of_nonneg_left hUp hμ
  have hU2 := mul_le_mul_of_nonneg_left hcurv (mul_nonneg hK.le ht)
  have hUbound : μ*U ≤ K*t*a := by nlinarith only [hU1,hU2]
  have hUt := mul_le_mul_of_nonneg_left hLm (mul_nonneg hK.le ht)
  have hUL : U ≤ K^2*L*s*t := by nlinarith only [hUp,hUt]
  have hUZ := mul_le_mul_of_nonneg_right hUL (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hz)
  have hheight : 2*U*z/L ≤ 2*K^2*s*t*z := by
    apply (div_le_iff₀ hLp).mpr
    nlinarith only [hUZ]
  have hinside : μ*M+μ*U+g+2*U*z/L ≤ K*a+K*t*a+g+2*K^2*s*t*z := by
    linarith only [hMbound,hUbound,hheight]
  have hp := mul_le_mul hcount hinside (by linarith only [hM0,hU0,hg,hheight0]) hs.le
  nlinarith only [hp]

end
end StrongSilver
