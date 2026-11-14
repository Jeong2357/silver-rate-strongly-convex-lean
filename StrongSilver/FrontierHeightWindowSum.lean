-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FrontierSubtreeLabels
import StrongSilver.IndexedWindowExactLabels
import StrongSilver.FinitePropFilteredSum

namespace StrongSilver
open ScheduleTree BinaryForest
noncomputable section
set_option maxHeartbeats 6500000

/-- Exact summation of a signed original height-window charge over
all actual disjoint frontier subtrees. -/
theorem frontier_height_window_sum (φ : ℝ → ℝ) (hφ : Monotone φ) (P low s : ℝ)
    (start : ℕ) (κ : ℝ) (t : ScheduleTree) (hc : t.Cartesian) (F : ScheduleNode → ℝ) :
    ((indexedFrontier φ s start κ t).map fun q =>
      ((labels (indexedHeightWindow φ P low q.start q.reserve q.source)).map F).sum).sum =
    ((labels (t.indexedTree start κ)).map fun b =>
      if φ b.pivot ≤ s ∧ P < φ b.pivot ∧ low < nodePaddedHeight φ P b then F b else 0).sum := by
  let Q := fun b : ScheduleNode => if P < φ b.pivot ∧ low < nodePaddedHeight φ P b then F b else 0
  have hPer (q : ScheduleNode) (hq : q ∈ indexedFrontier φ s start κ t) :
      ((labels (indexedHeightWindow φ P low q.start q.reserve q.source)).map F).sum =
      ((labels (q.source.indexedTree q.start q.reserve)).map Q).sum := by
    rw [indexed_height_window_labels φ hφ P low q.start q.reserve q.source (indexedFrontier_source_cartesian hc hq),
      list_filter_prop_sum_eq]
  have hFirst : ((indexedFrontier φ s start κ t).map fun q =>
      ((labels (indexedHeightWindow φ P low q.start q.reserve q.source)).map F).sum).sum =
      ((indexedFrontier φ s start κ t).map fun q => ((labels (q.source.indexedTree q.start q.reserve)).map Q).sum).sum := by
    congr 1
    exact List.map_congr_left hPer
  rw [hFirst,← list_sum_map_flatMap,indexedFrontier_subtree_labels φ hφ s start κ t hc,list_filter_prop_sum_eq]
  congr 1
  apply List.map_congr_left
  intro b hb
  dsimp only [Q]
  by_cases h1 : φ b.pivot ≤ s
  · by_cases h2 : P < φ b.pivot ∧ low < nodePaddedHeight φ P b
    · simp only [if_pos h1,if_pos h2,if_pos (And.intro h1 h2)]
    · have hh : ¬ (φ b.pivot ≤ s ∧ P < φ b.pivot ∧ low < nodePaddedHeight φ P b) := fun hh => h2 hh.2
      simp only [if_pos h1,if_neg h2,if_neg hh]
  · have hh : ¬ (φ b.pivot ≤ s ∧ P < φ b.pivot ∧ low < nodePaddedHeight φ P b) := fun hh => h1 hh.1
    simp only [if_neg h1,if_neg hh]

end
end StrongSilver
