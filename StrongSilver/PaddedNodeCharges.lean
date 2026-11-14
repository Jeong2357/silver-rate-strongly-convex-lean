-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PaddedTreeInput
import StrongSilver.ReservedNodeTransform

namespace StrongSilver.ScheduleTree
open Scalar.SignedIntervals
noncomputable section
set_option maxHeartbeats 3600000

theorem paddedInput_height_weight (φ : ℝ → ℝ) {P κ : ℝ} (hP : 0 < P) (hκ : 0 ≤ κ) (hzero : φ 0 ≤ 0)
    (t : ScheduleTree) (hroot : P < φ t.rootStep) :
    (paddedInput φ hP hκ hzero t hroot).weight = Real.exp (nu*nodeHeight φ P (t,κ)) := by
  rw [paddedInput_weight,Real.rpow_def_of_pos (sub_pos.mpr hroot)]
  unfold nodeHeight
  rw [mul_comm]

theorem paddedInput_excess (φ : ℝ → ℝ) {P κ : ℝ} (hP : 0 < P) (hκ : 0 ≤ κ) (hzero : φ 0 ≤ 0)
    (t : ScheduleTree) (hroot : P < φ t.rootStep) :
    (paddedInput φ hP hκ hzero t hroot).excess = nodeExcess φ P (t,κ) := by
  have hh := (paddedInput φ hP hκ hzero t hroot).decrease_identity
  rw [paddedInput_decrease,paddedInput_height_weight,paddedInput_gain] at hh
  unfold nodeExcess
  linarith only [hh]

theorem nodeExcess_nonnegative (φ : ℝ → ℝ) {P κ : ℝ} (hP : 0 < P) (hκ : 0 ≤ κ) (hzero : φ 0 ≤ 0)
    (t : ScheduleTree) (hroot : P < φ t.rootStep) : 0 ≤ nodeExcess φ P (t,κ) := by
  rw [← paddedInput_excess φ hP hκ hzero t hroot]
  exact (paddedInput φ hP hκ hzero t hroot).excess_nonnegative

/-- Quantitative unbalanced charge for canonical original tree data. -/
theorem node_unbalanced_charge : ∃ c > 0, ∀ φ : ℝ → ℝ, ∀ P κ δ : ℝ, ∀ t : ScheduleTree,
    0 < P → 0 ≤ κ → φ 0 ≤ 0 → P < φ t.rootStep → 0 ≤ δ → δ ≤ 1 →
    ¬ PaddedBalanced φ P κ δ t →
    c*Real.exp (nu*nodeHeight φ P (t,κ))*δ^2 ≤ nodeExcess φ P (t,κ) := by
  obtain ⟨c,hc,hcharge⟩ := PaddedSplitInput.unbalanced_excess_charge
  refine ⟨c,hc,?_⟩
  intro φ P κ δ t hP hκ hzero hroot hδ hδ1 hbad
  have hs : ¬ (paddedInput φ hP hκ hzero t hroot).Balanced δ := by
    intro hs
    exact hbad ((paddedInput_balance_iff φ hP hκ hzero t hroot δ).mp hs)
  have hh := hcharge (paddedInput φ hP hκ hzero t hroot) δ hδ hδ1 hs
  rwa [paddedInput_height_weight,paddedInput_excess] at hh

/-- The signed gain charge also uses the canonical original words. -/
theorem node_absolute_gain_charge : ∃ C > 0, ∀ φ : ℝ → ℝ, ∀ P κ : ℝ, ∀ t : ScheduleTree,
    0 < P → 0 ≤ κ → φ 0 ≤ 0 → P < φ t.rootStep →
    Real.exp (nu*nodeHeight φ P (t,κ))*|paddedRootGain φ P κ t| ≤
      C*Real.exp (nu*nodeHeight φ P (t,κ))+C*nodeExcess φ P (t,κ) := by
  obtain ⟨C,hC,hcharge⟩ := PaddedSplitInput.weighted_gain_charge
  refine ⟨C,hC,?_⟩
  intro φ P κ t hP hκ hzero hroot
  have hh := hcharge (paddedInput φ hP hκ hzero t hroot)
  rwa [paddedInput_height_weight,paddedInput_gain,paddedInput_excess] at hh

end
end StrongSilver.ScheduleTree
