-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PaddedTreeInput

namespace StrongSilver.ScheduleTree
noncomputable section
set_option maxHeartbeats 2600000

/-- Padded nonterminal balance gives the exact offset-one ratio
conditions used in the actual grouped trajectory construction. -/
theorem paddedBalanced_to_silverBalanced {φ : ℝ → ℝ} {P δ : ℝ} {t : ScheduleTree}
    (hP : 1 ≤ P) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hpad : P ≤ δ*φ t.rootStep)
    (hb : PaddedBalanced φ P 0 δ t) : SilverBalanced φ (4*δ) t := by
  cases t with
  | leaf hw => exact False.elim hb
  | split l b r =>
    have hd := (div_le_iff₀ (sub_pos.mpr hb.1)).mp hb.2.2.2
    apply silverBalanced_of_log_balance hP hb.1 hδ hδ1 hpad hb.2.1 _ hd
    simpa only [add_zero,gapPrefix,transformedWord] using hb.2.2.1

end
end StrongSilver.ScheduleTree
