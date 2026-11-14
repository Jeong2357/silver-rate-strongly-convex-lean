-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FiniteBadForest

namespace StrongSilver.ScheduleTree
noncomputable section
set_option maxHeartbeats 3600000

/-- A finite height window with a positive separation on edges inside
good components. An edge ending at a bad vertex is deliberately free. -/
def SpacedGoodTree (good : ScheduleTree → Bool) (height : ScheduleTree → ℝ)
    (spacing low high : ℝ) : ScheduleTree → Prop
  | .leaf _ => True
  | .split l b r =>
    low ≤ height (.split l b r) ∧ height (.split l b r) ≤ high ∧
    SpacedGoodTree good height spacing low high l ∧ SpacedGoodTree good height spacing low high r ∧
    (good (.split l b r) = true → 0 < goodComponentHeight good l →
      spacing ≤ height (.split l b r)-height l) ∧
    (good (.split l b r) = true → 0 < goodComponentHeight good r →
      spacing ≤ height (.split l b r)-height r)

theorem good_component_scaled_height {good : ScheduleTree → Bool} {height : ScheduleTree → ℝ}
    {spacing low high : ℝ} {t : ScheduleTree}
    (h : SpacedGoodTree good height spacing low high t)
    (hn : 0 < goodComponentHeight good t) :
    (goodComponentHeight good t : ℝ)*spacing ≤ height t-low+spacing := by
  induction t with
  | leaf hw => simp only [goodComponentHeight] at hn; omega
  | split l b r il ir =>
    have hg : good (.split l b r) = true := by
      by_contra hh
      simp only [goodComponentHeight,Bool.eq_false_iff.mpr hh,Bool.false_eq_true,↓reduceIte] at hn
      omega
    have hleft : (goodComponentHeight good l : ℝ)*spacing ≤ height (.split l b r)-low := by
      by_cases hz : goodComponentHeight good l = 0
      · rw [hz,Nat.cast_zero,zero_mul]
        linarith only [h.1]
      · have hpos : 0 < goodComponentHeight good l := Nat.pos_of_ne_zero hz
        have hi := il h.2.2.1 hpos
        have he := h.2.2.2.2.1 hg hpos
        linarith only [hi,he]
    have hright : (goodComponentHeight good r : ℝ)*spacing ≤ height (.split l b r)-low := by
      by_cases hz : goodComponentHeight good r = 0
      · rw [hz,Nat.cast_zero,zero_mul]
        linarith only [h.1]
      · have hpos : 0 < goodComponentHeight good r := Nat.pos_of_ne_zero hz
        have hi := ir h.2.2.2.1 hpos
        have he := h.2.2.2.2.2 hg hpos
        linarith only [hi,he]
    simp only [goodComponentHeight,hg,↓reduceIte,Nat.cast_add,Nat.cast_one]
    rcases le_total (goodComponentHeight good l) (goodComponentHeight good r) with hmax | hmax
    · rw [max_eq_right hmax]
      linarith only [hright]
    · rw [max_eq_left hmax]
      linarith only [hleft]

theorem spaced_good_components_bounded {good : ScheduleTree → Bool} {height : ScheduleTree → ℝ}
    {spacing low high : ℝ} {m : ℕ} {t : ScheduleTree}
    (hs : 0 < spacing) (hwindow : high-low < (m : ℝ)*spacing)
    (h : SpacedGoodTree good height spacing low high t) : AllGoodComponentsBounded good m t := by
  induction t with
  | leaf hw => trivial
  | split l b r il ir =>
    refine ⟨?_,il h.2.2.1,ir h.2.2.2.1⟩
    by_cases hz : goodComponentHeight good (.split l b r) = 0
    · rw [hz]; exact Nat.zero_le _
    · have hpos := Nat.pos_of_ne_zero hz
      have hh := good_component_scaled_height h hpos
      have hlt : (goodComponentHeight good (.split l b r) : ℝ) < (m : ℝ)+1 := by
        apply (mul_lt_mul_iff_right₀ hs).mp
        nlinarith only [hh,hwindow,h.2.1]
      have hnat : goodComponentHeight good (.split l b r) < m+1 := by exact_mod_cast hlt
      omega

/-- The forest counting estimate used to absorb the positive per-pivot
error by the excess at unbalanced vertices. -/
theorem spaced_forest_node_bound {good : ScheduleTree → Bool} {height : ScheduleTree → ℝ}
    {spacing low high : ℝ} {m : ℕ} {t : ScheduleTree}
    (hs : 0 < spacing) (hwindow : high-low < (m : ℝ)*spacing)
    (h : SpacedGoodTree good height spacing low high t) :
    t.nodeCount ≤ 2^(m+1)*(badNodeCount good t+1) :=
  nodeCount_bound_by_bad_count (spaced_good_components_bounded hs hwindow h)

end
end StrongSilver.ScheduleTree
