-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.GoodThroughFailure
import StrongSilver.GoodVisibleDepth

namespace StrongSilver.BinaryForest
open Real Set MeasureTheory
noncomputable section
variable {α : Type*}
set_option maxHeartbeats 6800000

local instance incompleteVisibleDecidable (G : α → Bool) (H : α → ℝ) (parent : Option α) (x : α) (y : ℝ) :
    Decidable (GoodHeightVisible G H parent x y) := Classical.propDecidable _
local instance incompleteThroughDecidable (G : α → Bool) (n : ℕ) (t : BinaryTree α) : Decidable (GoodThrough G n t) := Classical.propDecidable _

/-- Integral exclusion count for visible good roots that fail the
complete-good-subtree condition. -/
def incompleteVisibleTotal (G : α → Bool) (H : α → ℝ) (v : ℝ) (n : ℕ)
    (parent : Option α) : BinaryTree α → ℝ → ℝ
  | .nil => fun _ => 0
  | t@(.node x l r) => fun y =>
      (if GoodHeightVisible G H parent x y ∧ ¬ GoodThrough G (n+2) t then Real.exp (v*y) else 0)+
        incompleteVisibleTotal G H v n (some x) l y+incompleteVisibleTotal G H v n (some x) r y

def goodVisibleThroughTotal (G : α → Bool) (H F : α → ℝ) (v : ℝ)
    (parent : Option α) (t : BinaryTree α) : ℕ → ℝ → ℝ
  | 0 => fun _ => 0
  | n+1 => fun y => goodVisibleDepthTotal G H F v n parent t y+goodVisibleThroughTotal G H F v parent t n y

theorem goodVisibleThroughTotal_integrable (G : α → Bool) (H F : α → ℝ) (v a b : ℝ)
    (parent : Option α) (t : BinaryTree α) (n : ℕ) :
    IntervalIntegrable (goodVisibleThroughTotal G H F v parent t n) volume a b := by
  induction n with
  | zero => exact intervalIntegrable_const
  | succ n ih => exact (goodVisibleDepthTotal_integrable G H F v a b n parent t).add ih

theorem goodVisibleThroughTotal_node (G : α → Bool) (H F : α → ℝ) (v : ℝ)
    (parent : Option α) (x : α) (l r : BinaryTree α) (n : ℕ) (y : ℝ) :
    goodVisibleThroughTotal G H F v parent (.node x l r) n y =
      (if GoodHeightVisible G H parent x y then Real.exp (v*y)*goodThroughScore G F n (.node x l r) else 0)+
        goodVisibleThroughTotal G H F v (some x) l n y+goodVisibleThroughTotal G H F v (some x) r n y := by
  classical
  induction n with
  | zero => simp [goodVisibleThroughTotal,goodThroughScore]
  | succ n ih =>
    simp only [goodVisibleThroughTotal,goodVisibleDepthTotal,goodThroughScore]
    rw [ih]
    split_ifs <;> ring

/-- The shortest missing-child path pays every failed visible subtree,
using only the already controlled missing-child vertex charge. -/
theorem incompleteVisibleTotal_le_through (G : α → Bool) (H M : α → ℝ) (v : ℝ)
    (hM : ∀ x, 0 ≤ M x) (n : ℕ) (parent : Option α) (t : BinaryTree α)
    (hC : GoodMissingCharge G M t) (y : ℝ) :
    incompleteVisibleTotal G H v n parent t y ≤ goodVisibleThroughTotal G H M v parent t (n+1) y := by
  classical
  induction t generalizing parent with
  | nil =>
    have hz : goodVisibleThroughTotal G H M v parent BinaryTree.nil (n+1) y = 0 := by
      generalize n+1 = k
      induction k with
      | zero => rfl
      | succ k ih => simp only [goodVisibleThroughTotal,goodVisibleDepthTotal,ih,add_zero]
    rw [hz]
    exact le_rfl
  | node x l r il ir =>
    have hl := il (some x) hC.2.1
    have hr := ir (some x) hC.2.2
    have hroot : (if GoodHeightVisible G H parent x y ∧ ¬ GoodThrough G (n+2) (.node x l r) then Real.exp (v*y) else 0) ≤
        (if GoodHeightVisible G H parent x y then Real.exp (v*y)*goodThroughScore G M (n+1) (.node x l r) else 0) := by
      by_cases hv : GoodHeightVisible G H parent x y
      · by_cases hf : ¬ GoodThrough G (n+2) (.node x l r)
        · have hc := incomplete_good_tree_charge G M hM n (.node x l r) hC hv.1 hf
          have hh := mul_le_mul_of_nonneg_left hc (Real.exp_pos (v*y)).le
          simpa [hv,hf] using hh
        · simp only [not_not] at hf
          simp only [hf,not_true_eq_false,and_false,↓reduceIte,if_pos hv]
          exact mul_nonneg (Real.exp_pos _).le (goodThroughScore_nonnegative G M hM (n+1) (.node x l r))
      · simp only [hv,false_and,↓reduceIte,le_refl]
    rw [goodVisibleThroughTotal_node]
    simp only [incompleteVisibleTotal]
    linear_combination hroot+hl+hr

theorem incompleteVisibleTotal_integrable (G : α → Bool) (H : α → ℝ) (v a b : ℝ)
    (n : ℕ) (parent : Option α) (t : BinaryTree α) :
    IntervalIntegrable (incompleteVisibleTotal G H v n parent t) volume a b := by
  classical
  induction t generalizing parent with
  | nil => exact intervalIntegrable_const
  | node x l r il ir =>
    have hroot : IntervalIntegrable (fun y => if GoodHeightVisible G H parent x y ∧
        ¬ GoodThrough G (n+2) (.node x l r) then Real.exp (v*y) else 0) volume a b := by
      by_cases hf : GoodThrough G (n+2) (.node x l r)
      · simp only [hf,not_true_eq_false,and_false,↓reduceIte]
        exact intervalIntegrable_const
      · simpa only [hf,not_false_eq_true,and_true] using goodHeightVisible_integrable G H v a b parent x
    exact (hroot.add (il (some x))).add (ir (some x))

end
end StrongSilver.BinaryForest
