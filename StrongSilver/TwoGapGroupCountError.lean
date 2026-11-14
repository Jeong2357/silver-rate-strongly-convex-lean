-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.TwoGapErrorAsymptotics

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 4000000

/-- The common error estimate allows any group count below the stated
polylogarithmic bound; in particular its depth need not be a function of log A. -/
theorem eventually_two_gap_group_error_by_count {K r γ : ℝ} (hK : 0 < K) (hr : 0 < r) :
    ∀ᶠ A : ℝ in atTop, ∀ μ M U L G : ℝ, G ≤ (Real.log A)^((1:ℝ)/1000) →
    0 ≤ μ → 0 ≤ M → 0 ≤ U → A/(K*(Real.log A)^((1:ℝ)/1000)) ≤ L →
    M ≤ K*A → U ≤ K*A*(Real.log A)^γ → μ*A ≤ A^(-r) →
    G*
      (μ*M+μ*U+workingGateFraction A+2*U*A^(-(1:ℝ)/20)/L) ≤ 1/Real.log A := by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    eventually_const_mul_log_rpow_mul_power_le_inverse_log ((1:ℝ)/1000) (4*K) (neg_neg_of_pos hr),
    eventually_const_mul_log_rpow_mul_power_le_inverse_log ((1:ℝ)/1000+γ) (4*K) (neg_neg_of_pos hr),
    eventually_const_mul_log_rpow_mul_power_le_inverse_log ((1:ℝ)/1000) 4 (by norm_num : -(67:ℝ)/500 < 0),
    eventually_const_mul_log_rpow_mul_power_le_inverse_log (2*((1:ℝ)/1000)+γ) (8*K^2) (by norm_num : -(1:ℝ)/20 < 0)]
    with A hA h1 h2 h3 h4
  intro μ M U L G hcount hμ hM hU hL hMp hUp hcurv
  have hApos := zero_lt_one.trans hA
  have hu := Real.log_pos hA
  have hs : 0 < (Real.log A)^((1:ℝ)/1000) := Real.rpow_pos_of_pos hu _
  have ht : 0 ≤ (Real.log A)^γ := (Real.rpow_pos_of_pos hu _).le
  have hz : 0 ≤ A^(-(1:ℝ)/20) := (Real.rpow_pos_of_pos hApos _).le
  have hg : 0 ≤ workingGateFraction A := (Real.rpow_pos_of_pos hApos _).le
  have hb := scaled_group_error hApos hK hs ht hz hg hμ hM hU hL hMp hUp hcurv hcount
  rw [Real.rpow_add hu] at h2
  have htwopow : (Real.log A)^(2*((1:ℝ)/1000)) = ((Real.log A)^((1:ℝ)/1000))^2 := by
    rw [show 2*((1:ℝ)/1000) = ((1:ℝ)/1000)*(2:ℕ) by norm_num,Real.rpow_mul_natCast hu.le]
  rw [Real.rpow_add hu,htwopow] at h4
  dsimp only [workingGateFraction] at hb ⊢
  nlinarith only [hb,h1,h2,h3,h4]

end
end StrongSilver
