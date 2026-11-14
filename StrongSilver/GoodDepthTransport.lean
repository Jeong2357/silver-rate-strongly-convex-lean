-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.IndexedScheduleTree
import Mathlib.Algebra.Order.BigOperators.Group.List

namespace StrongSilver.BinaryForest
noncomputable section
variable {α : Type*}
set_option maxHeartbeats 4800000

/-- Depth-j descendants whose entire path, including both endpoints,
is good. Leaves contribute no artificial vertex. -/
def goodDepthNodes (G : α → Bool) : ℕ → BinaryTree α → List α
  | _, .nil => []
  | 0, .node v _ _ => if G v then [v] else []
  | j+1, .node v l r => if G v then goodDepthNodes G j l++goodDepthNodes G j r else []

def goodDepthSum (G : α → Bool) (F : α → ℝ) (j : ℕ) (t : BinaryTree α) : ℝ :=
  ((goodDepthNodes G j t).map F).sum

/-- Sum over all possible original roots. Positions remain part of
labels, so this definition counts occurrences. -/
def goodDepthTotal (G : α → Bool) (F : α → ℝ) (j : ℕ) : BinaryTree α → ℝ
  | .nil => 0
  | t@(.node _ l r) => goodDepthSum G F j t+goodDepthTotal G F j l+goodDepthTotal G F j r

theorem goodDepthSum_nonnegative (G : α → Bool) (F : α → ℝ) (hF : ∀ v, 0 ≤ F v)
    (j : ℕ) (t : BinaryTree α) : 0 ≤ goodDepthSum G F j t := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨v,_,rfl⟩ := List.mem_map.mp hx
  exact hF v

/-- Advancing the depth discards possible ancestor roots. This
finite telescoping inequality is the unique-ancestor argument. -/
theorem goodDepthTotal_succ (G : α → Bool) (F : α → ℝ) (hF : ∀ v, 0 ≤ F v)
    (j : ℕ) (t : BinaryTree α) :
    goodDepthTotal G F (j+1) t ≤ goodDepthTotal G F j t-goodDepthSum G F j t := by
  induction t with
  | nil => simp [goodDepthTotal,goodDepthSum,goodDepthNodes]
  | node v l r il ir =>
    have hroot : goodDepthSum G F (j+1) (.node v l r) ≤ goodDepthSum G F j l+goodDepthSum G F j r := by
      by_cases hv : G v = true
      · simp only [goodDepthSum,goodDepthNodes,hv,↓reduceIte,List.map_append,List.sum_append]
        exact le_rfl
      · simp only [goodDepthSum,goodDepthNodes,Bool.eq_false_iff.mpr hv,Bool.false_eq_true,↓reduceIte,List.map_nil,List.sum_nil]
        exact add_nonneg (goodDepthSum_nonnegative G F hF j l) (goodDepthSum_nonnegative G F hF j r)
    simp only [goodDepthTotal]
    linear_combination hroot+il+ir

/-- Every descendant has at most one ancestor at a prescribed distance,
including when some paths are removed for containing a bad vertex. -/
theorem goodDepthTotal_le_zero (G : α → Bool) (F : α → ℝ) (hF : ∀ v, 0 ≤ F v)
    (j : ℕ) (t : BinaryTree α) : goodDepthTotal G F j t ≤ goodDepthTotal G F 0 t := by
  induction j with
  | zero => exact le_rfl
  | succ j ih =>
    have hs := goodDepthTotal_succ G F hF j t
    have hn := goodDepthSum_nonnegative G F hF j t
    linarith only [hs,hn,ih]

theorem goodDepthTotal_zero_le_labels (G : α → Bool) (F : α → ℝ) (hF : ∀ v, 0 ≤ F v)
    (t : BinaryTree α) : goodDepthTotal G F 0 t ≤ ((labels t).map F).sum := by
  induction t with
  | nil => exact le_rfl
  | node v l r il ir =>
    have hroot : goodDepthSum G F 0 (.node v l r) ≤ F v := by
      by_cases hv : G v = true
      · simp [goodDepthSum,goodDepthNodes,hv]
      · simpa only [goodDepthSum,goodDepthNodes,Bool.eq_false_iff.mpr hv,Bool.false_eq_true,↓reduceIte,List.map_nil,List.sum_nil] using hF v
    simp only [goodDepthTotal,labels,List.map_cons,List.map_append,List.sum_cons,List.sum_append]
    linear_combination hroot+il+ir

theorem goodDepthTotal_le_labels (G : α → Bool) (F : α → ℝ) (hF : ∀ v, 0 ≤ F v)
    (j : ℕ) (t : BinaryTree α) : goodDepthTotal G F j t ≤ ((labels t).map F).sum :=
  (goodDepthTotal_le_zero G F hF j t).trans (goodDepthTotal_zero_le_labels G F hF t)

end
end StrongSilver.BinaryForest
