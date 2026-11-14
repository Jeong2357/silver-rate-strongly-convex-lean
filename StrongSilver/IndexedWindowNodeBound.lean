-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.IndexedPositivePrune

namespace StrongSilver
open ScheduleTree BinaryForest
noncomputable section
set_option maxHeartbeats 4200000

def indexedHeightWindow (φ : ℝ → ℝ) (P low : ℝ) (start : ℕ) (κ : ℝ) (t : ScheduleTree) : BinaryTree ScheduleNode :=
  pruneBottom (nodePaddedHeight φ P) low (pruneBottom (fun q : ScheduleNode => φ q.pivot) P (indexedTree start κ t))

/-- The actual finite forest component needed in Section 4.6 has the
proved good-edge spacing and the stated height window. All labels are
original occurrences with their original interval positions and reserves. -/
theorem indexed_height_window_spaced {φ : ℝ → ℝ} (hφ : Monotone φ) {P low high κ δ : ℝ} {start : ℕ}
    (hP : 0 < P) (hκ : 0 ≤ κ) (hzero : φ 0 ≤ 0) (hδ : 0 ≤ δ) (hδmax : δ ≤ 1/100)
    (t : ScheduleTree) (hc : t.Cartesian) (hupper : φ t.rootStep ≤ P+Real.exp high) :
    SpacedGoodTree (rootGood (nodeBalancedBool φ P δ)) (rootHeight (nodePaddedHeight φ P))
      (Real.log rho-11*δ) low high (indexedHeightWindow φ P low start κ t) := by
  have hEdge := indexedTree_balanced_edge_spaced hP hκ hzero hδ hδmax start t
  have hPruned := pruneBottom_edge_spaced (guard := fun q : ScheduleNode => φ q.pivot) (low := P) hEdge
  have hUpper := indexedTree_positive_prune_below (start := start) (κ := κ) hφ t hc hupper
  exact pruneBottom_spaced hPruned hUpper

/-- Removing unbalanced original vertices bounds the node count in a
height window by its number of bad occurrences plus one root. -/
theorem indexed_height_window_node_bound {φ : ℝ → ℝ} (hφ : Monotone φ) {P low high κ δ : ℝ} {start m : ℕ}
    (hP : 0 < P) (hκ : 0 ≤ κ) (hzero : φ 0 ≤ 0) (hδ : 0 ≤ δ) (hδmax : δ ≤ 1/100)
    (hs : 0 < Real.log rho-11*δ) (hwindow : high-low < (m:ℝ)*(Real.log rho-11*δ))
    (t : ScheduleTree) (hc : t.Cartesian) (hupper : φ t.rootStep ≤ P+Real.exp high) :
    (indexedHeightWindow φ P low start κ t).numNodes ≤
      2^(m+1)*(badNodeCount (rootGood (nodeBalancedBool φ P δ)) (indexedHeightWindow φ P low start κ t)+1) :=
  spaced_forest_node_bound hs hwindow
    (indexed_height_window_spaced hφ hP hκ hzero hδ hδmax t hc hupper)

end
end StrongSilver
