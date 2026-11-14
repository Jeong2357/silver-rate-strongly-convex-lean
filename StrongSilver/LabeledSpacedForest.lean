-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.LabeledBadForest
import Mathlib.Data.Real.Basic

namespace StrongSilver.BinaryForest
noncomputable section
variable {α : Type*}
set_option maxHeartbeats 3600000

/-- A finite height window with a positive separation on edges inside
good components. An edge ending at a bad vertex is deliberately free. -/
def SpacedGoodTree (good : BinaryTree α → Bool) (height : BinaryTree α → ℝ)
    (spacing low high : ℝ) : BinaryTree α → Prop
  | .nil => True
  | .node b l r =>
    low ≤ height (.node b l r) ∧ height (.node b l r) ≤ high ∧
    SpacedGoodTree good height spacing low high l ∧ SpacedGoodTree good height spacing low high r ∧
    (good (.node b l r) = true → 0 < goodComponentHeight good l →
      spacing ≤ height (.node b l r)-height l) ∧
    (good (.node b l r) = true → 0 < goodComponentHeight good r →
      spacing ≤ height (.node b l r)-height r)

theorem good_component_scaled_height {good : BinaryTree α → Bool} {height : BinaryTree α → ℝ}
    {spacing low high : ℝ} {t : BinaryTree α}
    (h : SpacedGoodTree good height spacing low high t)
    (hn : 0 < goodComponentHeight good t) :
    (goodComponentHeight good t : ℝ)*spacing ≤ height t-low+spacing := by
  induction t with
  | nil => simp only [goodComponentHeight] at hn; omega
  | node b l r il ir =>
    have hg : good (.node b l r) = true := by
      by_contra hh
      simp only [goodComponentHeight,Bool.eq_false_iff.mpr hh,Bool.false_eq_true,↓reduceIte] at hn
      omega
    have hleft : (goodComponentHeight good l : ℝ)*spacing ≤ height (.node b l r)-low := by
      by_cases hz : goodComponentHeight good l = 0
      · rw [hz,Nat.cast_zero,zero_mul]
        linarith only [h.1]
      · have hpos : 0 < goodComponentHeight good l := Nat.pos_of_ne_zero hz
        have hi := il h.2.2.1 hpos
        have he := h.2.2.2.2.1 hg hpos
        linarith only [hi,he]
    have hright : (goodComponentHeight good r : ℝ)*spacing ≤ height (.node b l r)-low := by
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

theorem spaced_good_components_bounded {good : BinaryTree α → Bool} {height : BinaryTree α → ℝ}
    {spacing low high : ℝ} {m : ℕ} {t : BinaryTree α}
    (hs : 0 < spacing) (hwindow : high-low < (m : ℝ)*spacing)
    (h : SpacedGoodTree good height spacing low high t) : AllGoodComponentsBounded good m t := by
  induction t with
  | nil => trivial
  | node b l r il ir =>
    refine ⟨?_,il h.2.2.1,ir h.2.2.2.1⟩
    by_cases hz : goodComponentHeight good (.node b l r) = 0
    · rw [hz]; exact Nat.zero_le _
    · have hpos := Nat.pos_of_ne_zero hz
      have hh := good_component_scaled_height h hpos
      have hlt : (goodComponentHeight good (.node b l r) : ℝ) < (m : ℝ)+1 := by
        apply (mul_lt_mul_iff_right₀ hs).mp
        nlinarith only [hh,hwindow,h.2.1]
      have hnat : goodComponentHeight good (.node b l r) < m+1 := by exact_mod_cast hlt
      omega

/-- The forest counting estimate used to absorb the positive per-pivot
error by the excess at unbalanced vertices. -/
theorem spaced_forest_node_bound {good : BinaryTree α → Bool} {height : BinaryTree α → ℝ}
    {spacing low high : ℝ} {m : ℕ} {t : BinaryTree α}
    (hs : 0 < spacing) (hwindow : high-low < (m : ℝ)*spacing)
    (h : SpacedGoodTree good height spacing low high t) :
    t.numNodes ≤ 2^(m+1)*(badNodeCount good t+1) :=
  nodeCount_bound_by_bad_count (spaced_good_components_bounded hs hwindow h)

end
end StrongSilver.BinaryForest
