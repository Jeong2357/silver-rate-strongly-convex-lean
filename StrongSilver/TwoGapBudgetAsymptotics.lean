-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.UniformSignedBudgets
import StrongSilver.RealPolylogMargins

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 3600000

/-- The common signed-mass and height budgets for the two-gap
construction hold uniformly at large A. The lower scale may lose a
small power of log A; gamma < 1/40 leaves a fixed positive margin. -/
theorem eventually_two_gap_common_budgets {K c γ : ℝ} (hK : 0 < K) (hc : 0 < c)
    (hγ : γ < 1/40) : ∀ᶠ A : ℝ in atTop,
    ∀ L U N : ℝ, 0 ≤ U → 0 ≤ N →
    A/(K*(Real.log A)^((1:ℝ)/1000)) ≤ L →
    U ≤ K*A*(Real.log A)^γ → N ≤ K*A*(Real.log A)^(-(1:ℝ)/10+γ) →
    1000 ≤ L ∧ N ≤ L/1000 ∧ 2*U*N ≤ c*L^2 ∧ 2*U*A^(-(1:ℝ)/20) ≤ c*L := by
  have hrN : (1:ℝ)/1000+(-(1:ℝ)/10+γ) < 0 := by linarith only [hγ]
  have hrPair : 2*((1:ℝ)/1000)+γ+(-(1:ℝ)/10+γ) < 0 := by linarith only [hγ]
  have hNevent : ∀ᶠ u : ℝ in atTop, 1000*K^2*u^((1:ℝ)/1000+(-(1:ℝ)/10+γ)) ≤ 1 := by
    simpa only [pow_zero,mul_one] using
      eventually_const_mul_log_pow_mul_power_le 0 (1000*K^2) hrN zero_lt_one
  have hPevent : ∀ᶠ u : ℝ in atTop, 2*K^4*u^(2*((1:ℝ)/1000)+γ+(-(1:ℝ)/10+γ)) ≤ c := by
    simpa only [pow_zero,mul_one] using
      eventually_const_mul_log_pow_mul_power_le 0 (2*K^4) hrPair hc
  filter_upwards [eventually_gt_atTop (1:ℝ),Real.tendsto_log_atTop.eventually hNevent,
    Real.tendsto_log_atTop.eventually hPevent,
    eventually_const_mul_log_rpow_mul_power_le ((1:ℝ)/1000+γ) (2*K^2) (by norm_num : -(1:ℝ)/20 < 0) hc,
    eventually_const_mul_log_rpow_le_power ((1:ℝ)/1000) (1000*K) (by norm_num : (0:ℝ) < 1)]
    with A hA hsmallN hsmallPair hsmallZ hlarge
  intro L U N hU hN hL hUp hNp
  have hApos := zero_lt_one.trans hA
  have hu : 0 < Real.log A := Real.log_pos hA
  have hs : 0 < (Real.log A)^((1:ℝ)/1000) := Real.rpow_pos_of_pos hu _
  have ht : 0 < (Real.log A)^γ := Real.rpow_pos_of_pos hu _
  have hn : 0 < (Real.log A)^(-(1:ℝ)/10+γ) := Real.rpow_pos_of_pos hu _
  have hz : 0 < A^(-(1:ℝ)/20) := Real.rpow_pos_of_pos hApos _
  have hNscaled : 1000*K^2*(Real.log A)^((1:ℝ)/1000)*(Real.log A)^(-(1:ℝ)/10+γ) ≤ 1 := by
    rw [Real.rpow_add hu] at hsmallN
    nlinarith only [hsmallN]
  have htwopow : (Real.log A)^(2*((1:ℝ)/1000)) = ((Real.log A)^((1:ℝ)/1000))^2 := by
    rw [show 2*((1:ℝ)/1000) = ((1:ℝ)/1000)*(2:ℕ) by norm_num,Real.rpow_mul_natCast hu.le]
  have hPairscaled : 2*K^4*((Real.log A)^((1:ℝ)/1000))^2*(Real.log A)^γ*(Real.log A)^(-(1:ℝ)/10+γ) ≤ c := by
    rw [Real.rpow_add hu,Real.rpow_add hu,htwopow] at hsmallPair
    nlinarith only [hsmallPair]
  have hZscaled : 2*K^2*(Real.log A)^((1:ℝ)/1000)*(Real.log A)^γ*A^(-(1:ℝ)/20) ≤ c := by
    rw [Real.rpow_add hu] at hsmallZ
    nlinarith only [hsmallZ]
  have hbudgets := uniform_signed_budgets hApos hK hs ht.le hn.le hU hN hz.le hc.le hL hUp hNp
    hNscaled hPairscaled hZscaled
  have hlarge0 : 1000 ≤ A/(K*(Real.log A)^((1:ℝ)/1000)) := by
    apply (le_div_iff₀ (mul_pos hK hs)).mpr
    rw [Real.rpow_one] at hlarge
    nlinarith only [hlarge]
  exact ⟨hlarge0.trans hL,hbudgets⟩

end
end StrongSilver
