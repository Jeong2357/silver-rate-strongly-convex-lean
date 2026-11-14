-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.GoodThroughSourceBalance
import StrongSilver.IndexedSubtreeLabels

namespace StrongSilver
open ScheduleTree BinaryForest Real Filter
noncomputable section
set_option maxHeartbeats 4400000

/-- The actual complete-good-subtree condition in pair availability
supplies the original-source balance required by the finite two-gap
trajectory, at every depth. -/
theorem eventually_band_goodThrough_balance : ∀ᶠ u : ℝ in atTop,
    ∀ κ B μ : ℝ, ∀ h : List ℝ, ∀ q : ScheduleNode, ∀ n : ℕ,
    0 < κ → 1 < B → B ≤ κ/128 → u ≤ firstAverageLogScale B → 0 < μ → μ*B ≤ 1/2 →
    q ∈ labels ((cartesian h).indexedTree 0 κ) →
    GoodThrough (bandGoodBool B μ u) n (q.source.indexedTree q.start q.reserve) →
    completeThrough n q.source ∧ balancedThrough (cappedStep μ B) (4*bandTolerance u) n q.source := by
  filter_upwards [eventually_band_good_source_balance] with u H
  intro κ B μ h q n hκ hB hBκ hU hμ hμB hq hg
  have hSub := indexedTree_subtree_labels hq
  apply goodThrough_indexed_source_balance (bandGoodBool B μ u) (cappedStep μ B) (4*bandTolerance u) n q.start q.reserve q.source _ hg
  intro p hp hG
  exact H κ B μ h p hκ hB hBκ hU hμ hμB (hSub.subset hp) hG

end
end StrongSilver
