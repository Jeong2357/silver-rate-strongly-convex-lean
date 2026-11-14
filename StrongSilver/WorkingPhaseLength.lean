-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ScalarPaddingPower
import StrongSilver.QuadraticPaddingPower
import StrongSilver.PhaseNormPadding

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 1000000

theorem eventually_working_phase_length {K : ℝ} (hK : 1 ≤ K) : ∀ᶠ A : ℝ in atTop,
    ∀ (R : ℂ) (D a P b J q T C e : ℝ),
      A^((49 : ℝ)/50) ≤ P → 1 ≤ b → b ≤ A^((201 : ℝ)/200) → 0 ≤ J →
      J ≤ A^(-(1 : ℝ)/5)*‖R‖+K*A^((1 : ℝ)/2) → 1/K ≤ q → q*D^2 = (b-1)*J →
      0 ≤ C → C ≤ K*A^((3 : ℝ)/1000) → T ≤ A^((51 : ℝ)/50) →
      0 ≤ e → 0 ≤ a → a ≤ C*e → e^2 = A^(-(3 : ℝ)/25)*T*(‖R‖+P) →
      ‖phasePoint R D a‖ ≤ (1+1/Real.log A)*(‖R‖+P) := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    eventually_const_mul_negative_power_le_inverse_log (by norm_num : -(37 : ℝ)/500 < 0) (3*K^2)]
    with A hA hδ
  intro R D a P b J q T C e hP hb hbA hJ0 hJ hq hpad hC0 hC hT he0 ha0 ha he
  have hA0 : 0 < A := zero_lt_one.trans hA
  have hP0 : 0 ≤ P := (Real.rpow_pos_of_pos hA0 _).le.trans hP
  have hQ : A^((49 : ℝ)/50) ≤ ‖R‖+P := hP.trans (le_add_of_nonneg_left (norm_nonneg R))
  have hD := quadratic_padding_power_bound hA.le hK hb (norm_nonneg R)
    (le_add_of_nonneg_right hP0) hJ0 hbA hQ hJ hq hpad
  have haP := scalar_padding_power_bound hA0 (zero_le_one.trans hK) hC0 he0 ha0 ha hC hT hQ he
  have hexp : A^(-(7 : ℝ)/40) ≤ A^(-(37 : ℝ)/500) :=
    Real.rpow_le_rpow_of_exponent_le hA.le (by norm_num)
  have hmul := mul_le_mul_of_nonneg_right hexp (sq_nonneg (‖R‖+P))
  have hDscale := mul_le_mul_of_nonneg_left hmul (show 0 ≤ 2*K^2 by positivity)
  have hpadding : D^2+a^2 ≤ (3*K^2*A^(-(37 : ℝ)/500))*(‖R‖+P)^2 := by
    norm_num at hD haP hDscale ⊢
    nlinarith only [hD,haP,hDscale]
  have hn := phase_norm_le_of_relative_padding hP0
    (show 0 ≤ 3*K^2*A^(-(37 : ℝ)/500) by positivity) hpadding
  have hm := mul_le_mul_of_nonneg_right hδ (add_nonneg (norm_nonneg R) hP0)
  nlinarith only [hn,hm]

end
end StrongSilver
