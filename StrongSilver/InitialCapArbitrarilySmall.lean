-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.InitialCapSmallness
import StrongSilver.CounterexampleThresholds

namespace StrongSilver
open Real Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 2400000

/-- The initial reserve construction permits any further absolute cap
smallness needed by the finite two-gap construction. -/
theorem exists_small_initial_cap_below {ε : ℝ} (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧ a ≤ ε ∧ a ≤ 1/128 ∧
      7*initialMarkedLogCoefficient a ≤ 1/2 ∧
      2*splitCoefficient*initialStableErrorCoefficient a ≤ powerLogMinimum/16 := by
  have hid : Tendsto (fun a : ℝ => a) (𝓝[>] (0:ℝ)) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hpos : ∀ᶠ a : ℝ in 𝓝[>] 0, 0 < a := self_mem_nhdsWithin
  have hcap := (tendsto_order.1 hid).2 (1/128) (by norm_num : (0:ℝ) < 1/128)
  have hsmall := (tendsto_order.1 hid).2 ε hε
  have htrackLimit := initialMarkedLogCoefficient_tendsto_zero.const_mul 7
  have herrorLimit := initialStableErrorCoefficient_tendsto_zero.const_mul (2*splitCoefficient)
  simp only [mul_zero] at htrackLimit herrorLimit
  have htrack := (tendsto_order.1 htrackLimit).2 (1/2) (by norm_num : (0:ℝ) < 1/2)
  have herror := (tendsto_order.1 herrorLimit).2 (powerLogMinimum/16)
    (div_pos powerLogMinimum_positive (by norm_num))
  have hall : ∀ᶠ a : ℝ in 𝓝[>] 0, 0 < a ∧ a ≤ ε ∧ a ≤ 1/128 ∧
      7*initialMarkedLogCoefficient a ≤ 1/2 ∧
      2*splitCoefficient*initialStableErrorCoefficient a ≤ powerLogMinimum/16 := by
    filter_upwards [hpos,hsmall,hcap,htrack,herror] with a ha hεa hca hta hea
    exact ⟨ha,hεa.le,hca.le,hta.le,hea.le⟩
  exact hall.exists

/-- The stronger finite curvature requirement is met by choosing a
smaller absolute cap; no assertion that μB tends to zero is needed. -/
theorem CounterexampleSequence.curvature_threshold_bound {a μ : ℝ} (S : CounterexampleSequence a) (j : ℕ)
    (hμ : 0 ≤ μ) (hμu : μ ≤ 9/(8*S.kappa j)) : μ*S.threshold j ≤ (9/8:ℝ)*a := by
  have hκ : 0 < S.kappa j := lt_of_lt_of_le (by norm_num) (S.kappa_ge_two j)
  have hacap : 0 < a*S.kappa j := (S.threshold_positive j).trans_le (S.threshold_le_cap j)
  have ha : 0 < a := (mul_pos_iff_of_pos_right hκ).mp hacap
  have hμα : μ*S.threshold j ≤ μ*(a*S.kappa j) := mul_le_mul_of_nonneg_left (S.threshold_le_cap j) hμ
  have hμκ : μ*S.kappa j ≤ 9/8 := by
    have hh := (le_div_iff₀ (show 0 < 8*S.kappa j by positivity)).mp hμu
    nlinarith only [hh]
  have hbound := mul_le_mul_of_nonneg_right hμκ ha.le
  nlinarith only [hμα,hbound]

end
end StrongSilver
