-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ShortBalancedEdges
import StrongSilver.PositionedWindowExcess

namespace StrongSilver
open ScheduleTree
noncomputable section
set_option maxHeartbeats 4200000

def ShortWindowEdge (φ : ℝ → ℝ) (P a b : ℝ) (q : ParentedScheduleNode) : Prop :=
  ∃ p : ScheduleNode, q.parent = some p ∧
    P < φ p.pivot ∧ 0 ≤ p.reserve ∧ P < φ q.node.pivot ∧
    a < nodeHeight φ P (p.source,p.reserve) ∧ nodeHeight φ P (p.source,p.reserve) ≤ b ∧
    a < parentedHeight φ P q ∧ parentedHeight φ P q ≤ b ∧
    parentedHeight φ P q ≤ nodeHeight φ P (p.source,p.reserve) ∧
    nodeHeight φ P (p.source,p.reserve)-parentedHeight φ P q < 3*visibilitySpacing

local instance (φ : ℝ → ℝ) (P a b : ℝ) (q : ParentedScheduleNode) : Decidable (ShortWindowEdge φ P a b q) := Classical.propDecidable _

def shortWindowWeight (φ : ℝ → ℝ) (P a b : ℝ) (q : ParentedScheduleNode) : ℝ :=
  if ShortWindowEdge φ P a b q then Real.exp (nu*parentedHeight φ P q) else 0

/-- Short-edge weight is bounded by the window's actual excess sum.
The factor three includes the parent multiplicity, which is at most two. -/
theorem short_window_weight_charge : ∃ c₀ > 0,
    ∀ φ : ℝ → ℝ, ∀ P κ a b : ℝ, ∀ t : ScheduleTree,
    0 < P → 0 ≤ κ → φ 0 ≤ 0 →
    c₀*((parentedNodes 0 κ none t).map (shortWindowWeight φ P a b)).sum ≤
      3*((parentedNodes 0 κ none t).map fun q => windowNodeExcess φ P a b q.node).sum := by
  obtain ⟨c₀,hc₀,hcharge⟩ := short_edge_excess_charge
  refine ⟨c₀,hc₀,?_⟩
  intro φ P κ a b t hP hκ hzero
  let F := windowNodeExcess φ P a b
  have hF : ∀ q, 0 ≤ F q := windowNodeExcess_nonnegative φ hP hzero a b
  have hpoint : ∀ q ∈ parentedNodes 0 κ none t,
      c₀*shortWindowWeight φ P a b q ≤ F q.node+optionalNodeCharge F q.parent := by
    intro q hq
    unfold shortWindowWeight
    by_cases hs : ShortWindowEdge φ P a b q
    · rw [if_pos hs]
      obtain ⟨p,hparent,hpp,hpκ,hcp,hpa,hpb,hca,hcb,horder,hshort⟩ := hs
      have hcκ := parentedNodes_reserve_nonnegative hκ hq
      have he := parentedNodes_actual_edge hq hparent
      have hh := hcharge φ P p q.node he hP hpκ hcκ hzero hpp hcp horder hshort
      have hpF : F p = nodeExcess φ P (p.source,p.reserve) :=
        if_pos ⟨hpp,hpκ,hpa,hpb⟩
      have hcF : F q.node = nodeExcess φ P (q.node.source,q.node.reserve) :=
        if_pos ⟨hcp,hcκ,hca,hcb⟩
      rw [hparent,optionalNodeCharge,hpF,hcF]
      simpa only [parentedHeight,add_comm] using hh
    · rw [if_neg hs,mul_zero]
      exact add_nonneg (hF q.node) (optionalNodeCharge_nonnegative F hF q.parent)
  have hsum := List.sum_le_sum hpoint
  rw [List.sum_map_mul_left,List.sum_map_add] at hsum
  have hparent := parent_charge_multiplicity_root F hF κ t
  dsimp only [F] at *
  linear_combination hsum+hparent

theorem band_short_window_weight_charge : ∃ c₀ > 0,
    ∀ κ B cap μ u : ℝ, ∀ h : List ℝ,
    0 ≤ κ → 0 ≤ B → BandIntegralBounds κ B cap μ u h →
    c₀*((parentedNodes 0 κ none (cartesian h)).map
      (shortWindowWeight (cappedStep μ B) (bandPad u) (outerBandLow u) (outerBandHigh u))).sum ≤
        3*bandExcessConstant*weightedCount h cap := by
  obtain ⟨c₀,hc₀,H⟩ := short_window_weight_charge
  refine ⟨c₀,hc₀,?_⟩
  intro κ B cap μ u h hκ hB hIntegral
  have hh := H (cappedStep μ B) (bandPad u) κ (outerBandLow u) (outerBandHigh u) (cartesian h)
    (Real.exp_pos _) hκ (by simp only [cappedStep,if_pos hB,logarithmicStep_zero,le_refl])
  rw [band_windowNodeExcess_sum hκ hB] at hh
  have he := mul_le_mul_of_nonneg_left hIntegral.excess_upper (by norm_num : (0:ℝ) ≤ 3)
  exact hh.trans (by simpa only [mul_assoc] using he)

end
end StrongSilver
