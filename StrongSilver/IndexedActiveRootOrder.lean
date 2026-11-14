-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.DepthPrefixPartition
import StrongSilver.FrontierSubtreeLabels

namespace StrongSilver
open ScheduleTree BinaryForest Real
noncomputable section
set_option maxHeartbeats 4200000

/-- Active transformed heights inherit the original Cartesian order
on every original positioned source subtree. -/
theorem indexedTree_active_root_order (φ : ℝ → ℝ) (hφ : Monotone φ) (P : ℝ)
    (start : ℕ) (κ : ℝ) (t : ScheduleTree) (hc : t.Cartesian) :
    ActiveRootOrder (fun q : ScheduleNode => P < φ q.pivot) (nodePaddedHeight φ P) (t.indexedTree start κ) := by
  induction t generalizing start κ with
  | leaf word => trivial
  | split l b r il ir =>
    refine ⟨?_,il start 0 hc.1,ir (start+l.word.length+1) κ hc.2.1⟩
    intro q hq hActive
    have hOrder := hφ (cartesian_word_le_root hc (indexedTree_pivot_step_mem hq))
    change Real.log (φ q.pivot-P) ≤ Real.log (φ b-P)
    exact Real.log_le_log (sub_pos.mpr hActive) (sub_le_sub_right hOrder P)

end
end StrongSilver
