-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ActualScheduleEdges
import StrongSilver.PaddedNodeCharges

namespace StrongSilver
open ScheduleTree
noncomputable section
set_option maxHeartbeats 3200000

def visibilitySpacing : ℝ := Real.log rho/4

def fixedBalanceTolerance : ℝ := min ((Real.log rho)/100) (1/1000)

theorem visibilitySpacing_positive : 0 < visibilitySpacing := div_pos log_rho_positive (by norm_num)

theorem fixedBalanceTolerance_positive : 0 < fixedBalanceTolerance := lt_min
  (div_pos log_rho_positive (by norm_num)) (by norm_num)

theorem fixedBalanceTolerance_le : fixedBalanceTolerance ≤ 1/100 :=
  (min_le_right _ _).trans (by norm_num)

/-- On a short actual edge, one endpoint fails the fixed balance
tolerance. This is the local input for the short-edge excess charge. -/
theorem short_edge_unbalanced {φ : ℝ → ℝ} {P : ℝ} {p c : ScheduleNode}
    (he : ScheduleChild p c) (hP : 0 < P) (hκ : 0 ≤ p.reserve) (hzero : φ 0 ≤ 0)
    (hshort : nodeHeight φ P (p.source,p.reserve)-nodeHeight φ P (c.source,c.reserve) < 3*visibilitySpacing) :
    ¬ PaddedBalanced φ P p.reserve fixedBalanceTolerance p.source ∨
      ¬ PaddedBalanced φ P c.reserve fixedBalanceTolerance c.source := by
  by_contra hn
  push_neg at hn
  have hh := actual_balanced_edge_spacing he hP hκ hzero fixedBalanceTolerance_positive.le fixedBalanceTolerance_le hn.1 hn.2
  have hlo := (abs_le.mp hh).1
  have hδ : fixedBalanceTolerance ≤ Real.log rho/100 := min_le_left _ _
  have hω := log_rho_positive
  dsimp only [visibilitySpacing] at hshort
  linarith only [hlo,hδ,hshort,hω]

/-- A short child's weight is charged to one of the two actual endpoint
excesses. The absolute constant is independent of the tree and schedule. -/
theorem short_edge_excess_charge : ∃ c₀ > 0,
    ∀ φ : ℝ → ℝ, ∀ P : ℝ, ∀ p c : ScheduleNode,
    ScheduleChild p c → 0 < P → 0 ≤ p.reserve → 0 ≤ c.reserve → φ 0 ≤ 0 →
    P < φ p.pivot → P < φ c.pivot →
    nodeHeight φ P (c.source,c.reserve) ≤ nodeHeight φ P (p.source,p.reserve) →
    nodeHeight φ P (p.source,p.reserve)-nodeHeight φ P (c.source,c.reserve) < 3*visibilitySpacing →
    c₀*Real.exp (nu*nodeHeight φ P (c.source,c.reserve)) ≤
      nodeExcess φ P (p.source,p.reserve)+nodeExcess φ P (c.source,c.reserve) := by
  obtain ⟨c₁,hc₁,hcharge⟩ := node_unbalanced_charge
  refine ⟨c₁*fixedBalanceTolerance^2,mul_pos hc₁ (sq_pos_of_pos fixedBalanceTolerance_positive),?_⟩
  intro φ P p c he hP hκp hκc hzero hpp hcp horder hshort
  have hpE := nodeExcess_nonnegative φ hP hκp hzero p.source hpp
  have hcE := nodeExcess_nonnegative φ hP hκc hzero c.source hcp
  rcases short_edge_unbalanced he hP hκp hzero hshort with hp | hc
  · have hh := hcharge φ P p.reserve fixedBalanceTolerance p.source hP hκp hzero hpp
      fixedBalanceTolerance_positive.le (fixedBalanceTolerance_le.trans (by norm_num)) hp
    have hw := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left horder nu_positive.le)
    have hh' := mul_le_mul_of_nonneg_left hw (mul_pos hc₁ (sq_pos_of_pos fixedBalanceTolerance_positive)).le
    linear_combination hh+hh'+hcE
  · have hh := hcharge φ P c.reserve fixedBalanceTolerance c.source hP hκc hzero hcp
      fixedBalanceTolerance_positive.le (fixedBalanceTolerance_le.trans (by norm_num)) hc
    linear_combination hh+hpE

end
end StrongSilver
