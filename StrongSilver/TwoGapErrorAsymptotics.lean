-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ScaledGroupError
import StrongSilver.FourPhaseDepthAsymptotics
import StrongSilver.RealPolylogMargins
import StrongSilver.WorkingNewGate

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 3600000

/-- The full finite group-count loss is O(1/log A), uniformly over
original schedules with the stated common scales and curvature bound. -/
theorem eventually_two_gap_group_error {K r γ : ℝ} (hK : 0 < K) (hr : 0 < r) :
    ∀ᶠ A : ℝ in atTop, ∀ μ M U L : ℝ,
    0 ≤ μ → 0 ≤ M → 0 ≤ U → A/(K*(Real.log A)^((1:ℝ)/1000)) ≤ L →
    M ≤ K*A → U ≤ K*A*(Real.log A)^γ → μ*A ≤ A^(-r) →
    (2:ℝ)^fourPhaseDepth (Real.log A)*
      (μ*M+μ*U+workingGateFraction A+2*U*A^(-(1:ℝ)/20)/L) ≤ 1/Real.log A := by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_fourPhaseGroupCount_le_power (by norm_num : (0:ℝ) < 1/1000)),
    eventually_const_mul_log_rpow_mul_power_le_inverse_log ((1:ℝ)/1000) (4*K) (neg_neg_of_pos hr),
    eventually_const_mul_log_rpow_mul_power_le_inverse_log ((1:ℝ)/1000+γ) (4*K) (neg_neg_of_pos hr),
    eventually_const_mul_log_rpow_mul_power_le_inverse_log ((1:ℝ)/1000) 4 (by norm_num : -(67:ℝ)/500 < 0),
    eventually_const_mul_log_rpow_mul_power_le_inverse_log (2*((1:ℝ)/1000)+γ) (8*K^2) (by norm_num : -(1:ℝ)/20 < 0)]
    with A hA hcount h1 h2 h3 h4
  intro μ M U L hμ hM hU hL hMp hUp hcurv
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

/-- Curvature perturbations of the endpoint gain coefficients are
smaller than the balance tolerance u^(-1/10). -/
theorem eventually_curvature_below_balance {K r : ℝ} (hr : 0 < r) :
    ∀ᶠ A : ℝ in atTop, K*A^(-r) ≤ (Real.log A)^(-(1:ℝ)/10) := by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    eventually_const_mul_log_rpow_mul_power_le ((1:ℝ)/10) K (neg_neg_of_pos hr) zero_lt_one]
    with A hA hh
  have hu := Real.log_pos hA
  have hp := mul_le_mul_of_nonneg_right hh (Real.rpow_pos_of_pos hu (-(1:ℝ)/10)).le
  have he : (Real.log A)^((1:ℝ)/10)*(Real.log A)^(-(1:ℝ)/10) = 1 := by
    rw [← Real.rpow_add hu]
    norm_num
  have he' : K*(Real.log A)^((1:ℝ)/10)*A^(-r)*(Real.log A)^(-(1:ℝ)/10) = K*A^(-r) := by
    calc
      _ = K*A^(-r)*((Real.log A)^((1:ℝ)/10)*(Real.log A)^(-(1:ℝ)/10)) := by ring
      _ = _ := by rw [he,mul_one]
  simpa only [he',one_mul] using hp

end
end StrongSilver
