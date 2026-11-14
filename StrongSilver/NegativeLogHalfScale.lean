-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.LogConsequences

namespace StrongSilver
open Real
noncomputable section
set_option maxHeartbeats 1000000

theorem log_one_add_div_half_scale {κ T x : ℝ} (hκ : 0 < κ) (hT : 0 < T)
    (hκT : κ/2 ≤ T) (hx : 0 ≤ x) :
    Real.log (1+x/T) ≤ 2*Real.log (1+x/κ) := by
  have hfrac : x/T ≤ (2*x)/κ := by
    apply (div_le_div_iff₀ hT hκ).mpr
    have hh := mul_le_mul_of_nonneg_left (show κ ≤ 2*T by linarith only [hκT]) hx
    nlinarith only [hh]
  have hpoly : 1+x/T ≤ (1+x/κ)^2 := by
    have hh : (2*x)/κ = 2*(x/κ) := by ring
    rw [hh] at hfrac
    nlinarith only [hfrac,sq_nonneg (x/κ)]
  have hh := Real.log_le_log (by positivity : 0 < 1+x/T) hpoly
  rw [Real.log_pow] at hh
  norm_num at hh
  exact hh

theorem negativeLogSum_half_scale {κ T : ℝ} (hκ : 0 < κ) (hT : 0 < T)
    (hκT : κ/2 ≤ T) (h : List ℝ) : negativeLogSum h T ≤ 2*negativeLogSum h κ := by
  induction h with
  | nil => simp [negativeLogSum]
  | cons b h ih =>
    change (if b < 0 then Real.log (1+|b|/T) else 0)+negativeLogSum h T ≤
      2*((if b < 0 then Real.log (1+|b|/κ) else 0)+negativeLogSum h κ)
    by_cases hb : b < 0
    · rw [if_pos hb,if_pos hb]
      have hh := log_one_add_div_half_scale hκ hT hκT (abs_nonneg b)
      linarith only [hh,ih]
    · rw [if_neg hb,if_neg hb]
      linarith only [ih]

end
end StrongSilver
