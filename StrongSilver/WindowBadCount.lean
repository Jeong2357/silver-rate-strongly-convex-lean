-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.IndexedWindowExactLabels

namespace StrongSilver.BinaryForest
noncomputable section
variable {α : Type*}
set_option maxHeartbeats 2200000

/-- Bad vertices of a pruned component are exactly the bad labels in
its occurrence list. The formula does not discard tied or equal labels. -/
theorem badNodeCount_eq_label_sum (G : α → Bool) (t : BinaryTree α) :
    badNodeCount (rootGood G) t = ((labels t).map fun q => if G q then 0 else 1).sum := by
  induction t with
  | nil => rfl
  | node v l r il ir =>
    simp only [badNodeCount,rootGood,labels,List.map_cons,List.map_append,List.sum_cons,List.sum_append,il,ir]
    by_cases hv : G v = true
    · simp only [hv,↓reduceIte]; omega
    · simp only [Bool.eq_false_iff.mpr hv,Bool.false_eq_true,↓reduceIte]; omega

theorem badNodeCount_real_eq_label_sum (G : α → Bool) (t : BinaryTree α) :
    (badNodeCount (rootGood G) t : ℝ) = ((labels t).map fun q => if G q then (0:ℝ) else 1).sum := by
  induction t with
  | nil => simp [badNodeCount,labels]
  | node v l r il ir =>
    simp only [badNodeCount,rootGood,labels,List.map_cons,List.map_append,List.sum_cons,List.sum_append,Nat.cast_add]
    by_cases hv : G v = true
    · simp only [hv,↓reduceIte,Nat.cast_zero]
      linear_combination il+ir
    · simp only [Bool.eq_false_iff.mpr hv,Bool.false_eq_true,↓reduceIte,Nat.cast_one]
      linear_combination il+ir

end
end StrongSilver.BinaryForest
