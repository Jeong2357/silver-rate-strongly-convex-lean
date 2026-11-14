-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PaddedNodeCharges
import StrongSilver.PaddedTreeSpacing

namespace StrongSilver.ScheduleTree
open Scalar.SignedIntervals
noncomputable section
set_option maxHeartbeats 2800000

def nodeLeftDrawdown (φ : ℝ → ℝ) : ScheduleTree → ℝ
  | .leaf _ => 0
  | .split l _ _ => l.gapDrawdown φ

theorem paddedInput_left_drawdown (φ : ℝ → ℝ) {P κ : ℝ} (hP : 0 < P) (hκ : 0 ≤ κ) (hzero : φ 0 ≤ 0)
    (t : ScheduleTree) (hroot : P < φ t.rootStep) :
    drawdown (paddedInput φ hP hκ hzero t hroot).left = nodeLeftDrawdown φ t := by
  cases t with
  | leaf hw => exact False.elim (not_lt_of_ge (hzero.trans hP.le) hroot)
  | split l b r => rfl

theorem node_drawdown_charge : ∃ c > 0, ∀ φ : ℝ → ℝ, ∀ P κ δ : ℝ, ∀ t : ScheduleTree,
    0 < P → 0 ≤ κ → φ 0 ≤ 0 → P < φ t.rootStep → δ ≤ 1 → PaddedBalanced φ P κ δ t →
    c*Real.exp (nu*nodeHeight φ P (t,κ))*(nodeLeftDrawdown φ t/(φ t.rootStep-P)) ≤ nodeExcess φ P (t,κ) := by
  obtain ⟨c,hc,hcharge⟩ := PaddedSplitInput.drawdown_excess_charge
  refine ⟨c,hc,?_⟩
  intro φ P κ δ t hP hκ hzero hroot hδ1 hb
  have hbal := (paddedInput_balance_iff φ hP hκ hzero t hroot δ).mpr hb
  have hh := hcharge (paddedInput φ hP hκ hzero t hroot) (hbal.2.2.trans hδ1)
  rwa [paddedInput_height_weight,paddedInput_left_drawdown,paddedInput_time,paddedInput_excess] at hh

end
end StrongSilver.ScheduleTree
