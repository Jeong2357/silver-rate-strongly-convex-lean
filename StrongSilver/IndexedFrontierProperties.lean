-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.IndexedFrontier

namespace StrongSilver.ScheduleTree
noncomputable section
set_option maxHeartbeats 2200000

theorem indexedFrontier_reserve_nonnegative {φ : ℝ → ℝ} {s κ : ℝ} {start : ℕ} {t : ScheduleTree} {q : ScheduleNode}
    (hκ : 0 ≤ κ) (hq : q ∈ indexedFrontier φ s start κ t) : 0 ≤ q.reserve := by
  induction t generalizing start κ with
  | leaf hw =>
    have he := List.mem_singleton.mp hq
    exact he ▸ hκ
  | split l b r il ir =>
    simp only [indexedFrontier] at hq
    split_ifs at hq with hb
    · rcases List.mem_append.mp hq with hl | hr
      · exact il (le_refl 0) hl
      · exact ir hκ hr
    · have he := List.mem_singleton.mp hq
      exact he ▸ hκ

theorem indexedFrontier_source_cartesian {φ : ℝ → ℝ} {s κ : ℝ} {start : ℕ} {t : ScheduleTree} {q : ScheduleNode}
    (hc : t.Cartesian) (hq : q ∈ indexedFrontier φ s start κ t) : q.source.Cartesian := by
  induction t generalizing start κ with
  | leaf hw =>
    have he := List.mem_singleton.mp hq
    exact he ▸ hc
  | split l b r il ir =>
    simp only [indexedFrontier] at hq
    split_ifs at hq with hb
    · rcases List.mem_append.mp hq with hl | hr
      · exact il hc.1 hl
      · exact ir hc.2.1 hr
    · have he := List.mem_singleton.mp hq
      exact he ▸ hc

end
end StrongSilver.ScheduleTree
