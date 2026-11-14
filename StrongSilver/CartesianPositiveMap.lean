-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CartesianTransformMap
import StrongSilver.PositivePartCut
import StrongSilver.HeightCutSelectors

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 2800000

namespace ScheduleTree

/-- Removing negative transformed steps preserves the same positive
Cartesian pivots and chronological tie order. -/
theorem positivePart_map_cartesian {φ : ℝ → ℝ} (hφ : StrictMono φ) (hzero : φ 0 = 0)
    {t : ScheduleTree} (hc : t.Cartesian) : (t.mapSteps (positivePartStep φ)).Cartesian := by
  induction t with
  | leaf hw =>
    intro x hx
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx
    apply max_le
    · have hh := hφ.monotone (hc b hb)
      rwa [hzero] at hh
    · exact le_rfl
  | split l b r il ir =>
    have hb : 0 < φ b := by simpa only [hzero] using hφ hc.2.2.1
    refine ⟨il hc.1,ir hc.2.1,?_,?_,?_⟩
    · exact hb.trans_le (le_max_left _ _)
    · intro x hx
      rw [mapSteps_word] at hx
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
      change max (φ a) 0 < max (φ b) 0
      rw [max_eq_left hb.le]
      exact max_lt (hφ (hc.2.2.2.1 a ha)) hb
    · intro x hx
      rw [mapSteps_word] at hx
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
      exact max_le_max (hφ.monotone (hc.2.2.2.2 a ha)) le_rfl

end ScheduleTree

theorem heightCut_positivePart {φ : ℝ → ℝ} {P y : ℝ} (hP : 0 ≤ P) (h : List ℝ) :
    heightCut (positivePartStep φ) P y h = heightCut φ P y h := by
  have hp : 0 < P+Real.exp y := add_pos_of_nonneg_of_pos hP (Real.exp_pos _)
  have he : (fun (_ : ℕ) b => decide (P+Real.exp y < positivePartStep φ b)) =
      (fun (_ : ℕ) b => decide (P+Real.exp y < φ b)) := by
    funext j b
    simp only [positivePartStep,lt_max_iff,not_lt_of_ge hp.le,or_false]
  unfold heightCut
  rw [he]

end
end StrongSilver
