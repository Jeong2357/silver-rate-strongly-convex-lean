-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FarChildMassCharge
import StrongSilver.ProtectedBadWeight

namespace StrongSilver
open ScheduleTree BinaryForest
noncomputable section
set_option maxHeartbeats 4000000

local instance nearBadChildDecidableGood (φ : ℝ → ℝ) (P κ δ : ℝ) (t : ScheduleTree) : Decidable (PaddedGood φ P κ δ t) := Classical.propDecidable _

def NearBadChildAt (φ : ℝ → ℝ) (P κ a b δ width : ℝ) (eligible : ℕ → ℝ → Bool)
    (t : ScheduleTree) (q : ParentedScheduleNode) : Prop :=
  q ∈ protectedWindowNodes φ P κ a b eligible t ∧ ¬ PaddedGood φ P q.node.reserve δ q.node.source ∧
    ∃ p : ScheduleNode, q.parent = some p ∧ nodePaddedHeight φ P p-parentedHeight φ P q ≤ width

/-- Each nearby bad child has a single actual parent occurrence. The
parent weight loses at most exp(nu*width), with no merging of equal pivots. -/
theorem near_bad_child_weight_charge (φ : ℝ → ℝ) (P κ a b δ width : ℝ)
    (eligible : ℕ → ℝ → Bool) (t : ScheduleTree) :
    (((parentedNodes 0 κ none t).filter fun q => @decide (NearBadChildAt φ P κ a b δ width eligible t q) (Classical.propDecidable _)).map
      (parentWeight φ P)).sum ≤
      Real.exp (nu*width)*((protectedWindowNodes φ P κ a b eligible t).map fun q =>
        if PaddedGood φ P q.node.reserve δ q.node.source then 0 else Real.exp (nu*parentedHeight φ P q)).sum := by
  classical
  let target := fun q : ParentedScheduleNode => decide
    (P < φ q.node.pivot ∧ eligible q.node.pivotIndex q.node.pivot = true ∧
      a < parentedHeight φ P q ∧ parentedHeight φ P q+3*visibilitySpacing ≤ b)
  let f := fun q : ParentedScheduleNode =>
    if PaddedGood φ P q.node.reserve δ q.node.source then (0:ℝ) else Real.exp (nu*parentedHeight φ P q)
  have hf (q : ParentedScheduleNode) : 0 ≤ f q := by dsimp only [f]; split_ifs <;> positivity
  have hh := list_filtered_sum_domination (fun q => decide (NearBadChildAt φ P κ a b δ width eligible t q))
    target (parentWeight φ P) (fun q => Real.exp (nu*width)*f q) (parentedNodes 0 κ none t)
    (fun q _ => mul_nonneg (Real.exp_pos _).le (hf q)) (by
      intro q hq hsel
      obtain ⟨hmem,hbad,p,hparent,hheight⟩ := of_decide_eq_true hsel
      refine ⟨(List.mem_filter.mp hmem).2,?_⟩
      dsimp only [f]
      rw [if_neg hbad,parentWeight,hparent]
      have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
        (show nodePaddedHeight φ P p ≤ parentedHeight φ P q+width by linarith only [hheight]) nu_positive.le)
      rw [mul_add,Real.exp_add] at he
      exact he.trans_eq (by ring))
  rw [List.sum_map_mul_left] at hh
  exact hh

end
end StrongSilver
