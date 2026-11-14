-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.InitialStableLogBudget
import StrongSilver.PowerLogFloor
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace StrongSilver
open Real Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 1800000

theorem initialMarkedLogCoefficient_tendsto_zero :
    Tendsto initialMarkedLogCoefficient (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hid : Tendsto (fun a : ℝ => a) (𝓝[>] (0 : ℝ)) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hs : Tendsto Real.sqrt (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).mono_left nhdsWithin_le_nhds
  have hslog : Tendsto (fun a : ℝ => Real.sqrt a*Real.log (1/a)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hh := (tendsto_log_mul_rpow_nhdsGT_zero (by norm_num : (0 : ℝ) < 1/2)).neg
    simp only [neg_zero] at hh
    apply hh.congr'
    exact Filter.Eventually.of_forall (fun a => by dsimp only; simp only [Real.sqrt_eq_rpow,one_div,Real.log_inv]; ring)
  have halog : Tendsto (fun a : ℝ => a*Real.log (1/a)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hh := (tendsto_log_mul_rpow_nhdsGT_zero (by norm_num : (0 : ℝ) < 1)).neg
    simp only [neg_zero,Real.rpow_one] at hh
    apply hh.congr'
    exact Filter.Eventually.of_forall (fun a => by dsimp only; rw [one_div,Real.log_inv]; ring)
  have hh := (((hs.const_mul (initialMarkedRankConstant*(1+1/nu))).add
    (hslog.const_mul initialMarkedRankConstant)).add (hid.const_mul (2/(1-nu)))).add (halog.const_mul (1/(1-nu)))
  simp only [mul_zero,add_zero] at hh
  apply hh.congr'
  exact Filter.Eventually.of_forall (fun a => by unfold initialMarkedLogCoefficient; ring)

theorem initialStableErrorCoefficient_tendsto_zero :
    Tendsto initialStableErrorCoefficient (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hid : Tendsto (fun a : ℝ => a) (𝓝[>] (0 : ℝ)) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hh := (hid.const_mul ((63/8)/(1-nu))).add (initialMarkedLogCoefficient_tendsto_zero.const_mul initialStablePriceConstant)
  simp only [mul_zero,add_zero] at hh
  exact hh

/-- The absolute cap can be chosen to preserve half of the original
tracked pivots and absorb the initial block remainder. -/
theorem exists_small_initial_cap : ∃ a : ℝ, 0 < a ∧ a ≤ 1/128 ∧
    7*initialMarkedLogCoefficient a ≤ 1/2 ∧
    2*splitCoefficient*initialStableErrorCoefficient a ≤ powerLogMinimum/16 := by
  have hid : Tendsto (fun a : ℝ => a) (𝓝[>] (0 : ℝ)) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hpos : ∀ᶠ a : ℝ in 𝓝[>] 0, 0 < a := self_mem_nhdsWithin
  have hcap := (tendsto_order.1 hid).2 (1/128) (by norm_num : (0 : ℝ) < 1/128)
  have htTrack := initialMarkedLogCoefficient_tendsto_zero.const_mul 7
  have htError := initialStableErrorCoefficient_tendsto_zero.const_mul (2*splitCoefficient)
  simp only [mul_zero] at htTrack htError
  have htrack := (tendsto_order.1 htTrack).2 (1/2) (by norm_num : (0 : ℝ) < 1/2)
  have herror := (tendsto_order.1 htError).2 (powerLogMinimum/16) (by have hh := powerLogMinimum_positive; positivity)
  have hevent : ∀ᶠ a : ℝ in 𝓝[>] 0, 0 < a ∧ a ≤ 1/128 ∧
      7*initialMarkedLogCoefficient a ≤ 1/2 ∧ 2*splitCoefficient*initialStableErrorCoefficient a ≤ powerLogMinimum/16 := by
    filter_upwards [hpos,hcap,htrack,herror] with a ha hca htr her
    exact ⟨ha,hca.le,htr.le,her.le⟩
  exact hevent.exists

end
end StrongSilver
