-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.NodeListCharges
import StrongSilver.OriginalNodeExcessSum

namespace StrongSilver
open ScheduleTree
noncomputable section
set_option maxHeartbeats 3200000

local instance (φ : ℝ → ℝ) (P κ δ : ℝ) (t : ScheduleTree) : Decidable (PaddedBalanced φ P κ δ t) := Classical.propDecidable _

def bandOriginalNodes (κ B μ u : ℝ) (h : List ℝ) : List (ScheduleTree × ℝ) :=
  nodesInHeightWindow (cappedStep μ B) (bandPad u) κ (outerBandLow u) (outerBandHigh u) (cartesian h)

theorem bandExcessSum_eq_original {κ B cap μ u : ℝ} (hB : 0 ≤ B) (h : List ℝ) :
    bandExcessSum κ B cap μ u h =
      ((bandOriginalNodes κ B μ u h).map (nodeExcess (cappedStep μ B) (bandPad u))).sum := by
  symm
  exact heightWindowExcess_eq_transformed
    (by simp only [cappedStep,if_pos hB,logarithmicStep_zero]) _ _ _ _ _

/-- The unbalanced-node and drawdown charges in the band use the
original node occurrences, the actual transformed signed words, and
exactly the excess sum controlled by the full-cut integral identity. -/
theorem band_node_charges : ∃ c₁ > 0, ∃ c₂ > 0, ∃ C > 0,
    ∀ κ B cap μ u δ : ℝ, ∀ h : List ℝ,
    0 ≤ κ → 0 ≤ B → 0 ≤ δ → δ ≤ 1 → BandIntegralBounds κ B cap μ u h →
    let qs := bandOriginalNodes κ B μ u h
    let φ := cappedStep μ B
    let P := bandPad u
    c₁*δ^2*(qs.map fun q => if PaddedBalanced φ P q.2 δ q.1 then 0 else Real.exp (nu*nodeHeight φ P q)).sum ≤
      bandExcessConstant*weightedCount h cap ∧
    c₂*(qs.map fun q => if PaddedBalanced φ P q.2 δ q.1 then
      Real.exp (nu*nodeHeight φ P q)*(nodeLeftDrawdown φ q.1/(φ q.1.rootStep-P)) else 0).sum ≤
      bandExcessConstant*weightedCount h cap ∧
    (qs.map fun q => Real.exp (nu*nodeHeight φ P q)*|paddedRootGain φ P q.2 q.1|).sum ≤
      C*(qs.map fun q => Real.exp (nu*nodeHeight φ P q)).sum+C*bandExcessConstant*weightedCount h cap := by
  obtain ⟨c₁,hc₁,c₂,hc₂,C,hC,H⟩ := node_list_charges
  refine ⟨c₁,hc₁,c₂,hc₂,C,hC,?_⟩
  intro κ B cap μ u δ h hκ hB hδ hδ1 hIntegral
  dsimp only
  have hzero : cappedStep μ B 0 = 0 := by simp only [cappedStep,if_pos hB,logarithmicStep_zero]
  have hvalid : ∀ q ∈ bandOriginalNodes κ B μ u h, 0 ≤ q.2 ∧ bandPad u < cappedStep μ B q.1.rootStep := by
    intro q hq
    exact ⟨nodesInHeightWindow_reserve_nonnegative hκ hq,nodesInHeightWindow_root_positive hq⟩
  obtain ⟨hb,hd,hg⟩ := H (cappedStep μ B) (bandPad u) δ (bandOriginalNodes κ B μ u h)
    (Real.exp_pos _) hzero.le hδ hδ1 hvalid
  have he := hIntegral.excess_upper
  rw [bandExcessSum_eq_original hB] at he
  refine ⟨hb.trans he,hd.trans he,?_⟩
  have hh := mul_le_mul_of_nonneg_left he hC.le
  linear_combination hg+hh

end
end StrongSilver
