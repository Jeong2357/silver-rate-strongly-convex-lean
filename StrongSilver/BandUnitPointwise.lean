-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandNonterminal
import StrongSilver.BandPadRatio
import StrongSilver.BandBadWeightBudget

namespace StrongSilver
open ScheduleTree Real Filter
noncomputable section
set_option maxHeartbeats 4200000

/-- The pointwise offset-one power and gain estimates (4.17), on the
actual protected band, with terminal reserves and exponential pad errors
discharged uniformly. -/
theorem eventually_band_unit_pointwise : ∀ᶠ u : ℝ in atTop,
    ∀ κ B μ δ : ℝ, ∀ h : List ℝ, ∀ q : ParentedScheduleNode,
    0 < κ → 1 < B → B ≤ κ/128 → u ≤ firstAverageLogScale B → 0 < μ → μ*B ≤ 1/2 →
    0 ≤ δ → δ ≤ 1/4 → q ∈ bandProtectedNodes κ B μ u h →
    PaddedBalanced (cappedStep μ B) (bandPad u) q.node.reserve δ q.node.source →
    paddedRootDecrease (cappedStep μ B) (bandPad u) q.node.reserve q.node.source ≤
      splitCoefficient*Real.exp (nu*parentedHeight (cappedStep μ B) (bandPad u) q)*rootGain (cappedStep μ B) q.node.source+
      splitCoefficient*δ*Real.exp (nu*parentedHeight (cappedStep μ B) (bandPad u) q)*|rootGain (cappedStep μ B) q.node.source|+
      16*splitCoefficient*Real.exp (nu*parentedHeight (cappedStep μ B) (bandPad u) q)*Real.exp (-u/100) ∧
    |rootGain (cappedStep μ B) q.node.source-paddedRootGain (cappedStep μ B) (bandPad u) q.node.reserve q.node.source| ≤
      2*nodeLeftDrawdown (cappedStep μ B) q.node.source/(cappedStep μ B q.node.pivot-bandPad u)+8*Real.exp (-u/100) := by
  filter_upwards [eventually_band_balanced_nonterminal,eventually_band_pad_small,eventually_band_pad_ratio]
    with u hNonterminal hSmall hRatio
  intro κ B μ δ h q hκ hB hBκ hU hμ hμB hδ hδmax hq hb
  have hh := of_decide_eq_true (List.mem_filter.mp hq).2
  have hmem := (List.mem_filter.mp hq).1
  have hz := hNonterminal κ B μ δ h q hκ hB hBκ hU hμ hμB hδ hδmax hmem hh.2.1 hb
  have hzero : cappedStep μ B 0 ≤ 0 := by simp only [cappedStep,if_pos (zero_lt_one.trans hB).le,logarithmicStep_zero,le_refl]
  have he : Real.exp (parentedHeight (cappedStep μ B) (bandPad u) q) = cappedStep μ B q.node.pivot-bandPad u :=
    Real.exp_log (sub_pos.mpr hh.1)
  have hsize := (hSmall.2 _ hh.2.2.1.le).1
  have hratio := hRatio.2 _ hh.2.2.1.le
  rw [he] at hsize hratio
  rw [hz] at hb ⊢
  have hPower := padded_balanced_unit_power hSmall.1 hzero hsize hδ hδmax hb
  have hGain := padded_balanced_unit_gain_error hSmall.1 hzero hsize hδ hδmax hb
  have h1 := mul_le_mul_of_nonneg_left hratio
    (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 16) split_coefficient_positive.le) (Real.exp_pos (nu*parentedHeight (cappedStep μ B) (bandPad u) q)).le)
  have h2 := mul_le_mul_of_nonneg_left hratio (by norm_num : (0:ℝ) ≤ 8)
  constructor
  · dsimp only [parentedHeight,nodeHeight,ScheduleNode.pivot] at hPower h1 ⊢
    linear_combination hPower+h1
  · dsimp only [ScheduleNode.pivot] at h2 ⊢
    linear_combination hGain+h2

end
end StrongSilver
