-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ReservedTreeNodes

namespace StrongSilver.ScheduleTree
noncomputable section

theorem cartesian_word_le_root {t : ScheduleTree} (hc : t.Cartesian) {b : ℝ} (hb : b ∈ t.word) : b ≤ t.rootStep := by
  cases t with
  | leaf hw => exact hc b hb
  | split l p r => exact split_word_le hc b hb

end
end StrongSilver.ScheduleTree
