-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.IndexedFrontierProperties

namespace StrongSilver.ScheduleTree
noncomputable section
set_option maxHeartbeats 2400000

/-- Every actual frontier gap root is unselected at the cutoff. For a
leaf the zero root is controlled by the cutoff's positive domain. -/
theorem indexedFrontier_root_upper {φ : ℝ → ℝ} {s κ : ℝ} {start : ℕ} {t : ScheduleTree} {q : ScheduleNode}
    (hzero : φ 0 ≤ s) (hq : q ∈ indexedFrontier φ s start κ t) : φ q.source.rootStep ≤ s := by
  induction t generalizing start κ with
  | leaf hw =>
    have he := List.mem_singleton.mp hq
    rw [he]
    exact hzero
  | split l b r il ir =>
    simp only [indexedFrontier] at hq
    split_ifs at hq with hp
    · rcases List.mem_append.mp hq with hl | hr
      · exact il hl
      · exact ir hr
    · have he := List.mem_singleton.mp hq
      rw [he]
      exact le_of_not_gt hp

end
end StrongSilver.ScheduleTree
