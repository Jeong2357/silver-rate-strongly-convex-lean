-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PaddedNodeDrawdown

namespace StrongSilver.ScheduleTree
noncomputable section
set_option maxHeartbeats 3600000

local instance (φ : ℝ → ℝ) (P κ δ : ℝ) (t : ScheduleTree) : Decidable (PaddedBalanced φ P κ δ t) := Classical.propDecidable _

/-- Summed charges on the actual original-node occurrence list. All
transform and reserve conditions are local numeric properties of the
listed nodes; the excesses and weights are canonical. -/
theorem node_list_charges : ∃ c₁ > 0, ∃ c₂ > 0, ∃ C > 0,
    ∀ φ : ℝ → ℝ, ∀ P δ : ℝ, ∀ qs : List (ScheduleTree × ℝ),
    0 < P → φ 0 ≤ 0 → 0 ≤ δ → δ ≤ 1 →
    (∀ q ∈ qs, 0 ≤ q.2 ∧ P < φ q.1.rootStep) →
    c₁*δ^2*(qs.map fun q => if PaddedBalanced φ P q.2 δ q.1 then 0 else Real.exp (nu*nodeHeight φ P q)).sum ≤
      (qs.map (nodeExcess φ P)).sum ∧
    c₂*(qs.map fun q => if PaddedBalanced φ P q.2 δ q.1 then
      Real.exp (nu*nodeHeight φ P q)*(nodeLeftDrawdown φ q.1/(φ q.1.rootStep-P)) else 0).sum ≤
      (qs.map (nodeExcess φ P)).sum ∧
    (qs.map fun q => Real.exp (nu*nodeHeight φ P q)*|paddedRootGain φ P q.2 q.1|).sum ≤
      C*(qs.map fun q => Real.exp (nu*nodeHeight φ P q)).sum+C*(qs.map (nodeExcess φ P)).sum := by
  obtain ⟨c₁,hc₁,hbad⟩ := node_unbalanced_charge
  obtain ⟨c₂,hc₂,hdraw⟩ := node_drawdown_charge
  obtain ⟨C,hC,hgain⟩ := node_absolute_gain_charge
  refine ⟨c₁,hc₁,c₂,hc₂,C,hC,?_⟩
  intro φ P δ qs hP hzero hδ hδ1 hvalid
  have hpointBad : ∀ q ∈ qs, c₁*δ^2*(if PaddedBalanced φ P q.2 δ q.1 then 0 else Real.exp (nu*nodeHeight φ P q)) ≤ nodeExcess φ P q := by
    intro q hq
    have hv := hvalid q hq
    by_cases hb : PaddedBalanced φ P q.2 δ q.1
    · rw [if_pos hb,mul_zero]
      exact nodeExcess_nonnegative φ hP hv.1 hzero q.1 hv.2
    · rw [if_neg hb]
      have hh := hbad φ P q.2 δ q.1 hP hv.1 hzero hv.2 hδ hδ1 hb
      linear_combination hh
  have hpointDraw : ∀ q ∈ qs, c₂*(if PaddedBalanced φ P q.2 δ q.1 then
      Real.exp (nu*nodeHeight φ P q)*(nodeLeftDrawdown φ q.1/(φ q.1.rootStep-P)) else 0) ≤ nodeExcess φ P q := by
    intro q hq
    have hv := hvalid q hq
    by_cases hb : PaddedBalanced φ P q.2 δ q.1
    · rw [if_pos hb]
      have hh := hdraw φ P q.2 δ q.1 hP hv.1 hzero hv.2 hδ1 hb
      linear_combination hh
    · rw [if_neg hb,mul_zero]
      exact nodeExcess_nonnegative φ hP hv.1 hzero q.1 hv.2
  have hb := List.sum_le_sum hpointBad
  have hd := List.sum_le_sum hpointDraw
  rw [List.sum_map_mul_left] at hb hd
  have hg := List.sum_le_sum (l := qs) (fun q hq =>
    hgain φ P q.2 q.1 hP (hvalid q hq).1 hzero (hvalid q hq).2)
  simp only [List.sum_map_add,List.sum_map_mul_left] at hg
  exact ⟨hb,hd,hg⟩

end
end StrongSilver.ScheduleTree
