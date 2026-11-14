-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.LinkedIncompleteDepth

namespace StrongSilver
open ScheduleTree BinaryForest Real Filter Set MeasureTheory
noncomputable section
set_option maxHeartbeats 4800000

/-- The depth-failure part of (4.25) is a bound on the actual
chronological linked gap count. -/
theorem eventually_band_linked_incomplete_budget : ∃ C > 0, ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ critical a b : ℝ, ∀ h : List ℝ,
    1 < κ → 1 < B → B ≤ cap → cap ≤ κ → B ≤ κ/128 → u ≤ firstAverageLogScale B →
    1/κ ≤ μ → μ ≤ 2/κ → μ*B ≤ 1/2 → a ≤ b →
    (∀ z ∈ h, 1-μ*z ≠ 0) → inverseChargeAbove (κ/4) h μ ≤ critical →
    critical ≤ 34*weightedCount h cap*cap^(-nu) → D κ h ≤ 1 →
    1 ≤ countAbove h B → κ^nu ≤ weightedCount h cap →
    (∫ y in a..b, linkedIncompleteObservable κ B μ u (fourPhaseDepth u+1) h y) ≤
      C*weightedCount h cap*u^((9:ℝ)/10)*(2:ℝ)^fourPhaseDepth u := by
  obtain ⟨C,hC,H⟩ := eventually_band_incomplete_depth
  refine ⟨C,hC,?_⟩
  filter_upwards [H] with u hBudget
  intro κ B cap μ critical a b h hκ hB hBcap hcapκ hBκ hU hμ hμu hμB hab hcrit hcritical hcriticalRank hD hcount hκW
  have hμ0 := (one_div_pos.mpr (zero_lt_one.trans hκ)).trans_le hμ
  have heq : linkedIncompleteObservable κ B μ u (fourPhaseDepth u+1) h = fun y =>
      incompleteVisibleTotal (bandGoodBool B μ u) (nodePaddedHeight (cappedStep μ B) (bandPad u))
        nu (fourPhaseDepth u+1) none ((cartesian h).indexedTree 0 κ) y := by
    funext y
    exact linkedIncompleteObservable_eq (fourPhaseDepth u+1) h hB hμ0 hμB
  rw [heq]
  exact hBudget κ B cap μ critical a b h hκ hB hBcap hcapκ hBκ hU hμ hμu hμB hab hcrit hcritical hcriticalRank hD hcount hκW

end
end StrongSilver
