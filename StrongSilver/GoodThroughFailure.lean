-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.GoodDepthTransport
import StrongSilver.LabeledWindowForest

namespace StrongSilver.BinaryForest
noncomputable section
variable {α : Type*}
set_option maxHeartbeats 5600000

def GoodThrough (G : α → Bool) : ℕ → BinaryTree α → Prop
  | 0, _ => True
  | _+1, .nil => False
  | n+1, t@(.node _ l r) => rootGood G t = true ∧ GoodThrough G n l ∧ GoodThrough G n r

def GoodMissingCharge (G : α → Bool) (M : α → ℝ) : BinaryTree α → Prop
  | .nil => True
  | t@(.node v l r) =>
    (G v = true → ¬ (rootGood G l = true ∧ rootGood G r = true) → 1 ≤ M v) ∧
      GoodMissingCharge G M l ∧ GoodMissingCharge G M r

def goodThroughScore (G : α → Bool) (F : α → ℝ) : ℕ → BinaryTree α → ℝ
  | 0, _ => 0
  | n+1,t => goodDepthSum G F n t+goodThroughScore G F n t

theorem goodThroughScore_nonnegative (G : α → Bool) (F : α → ℝ) (hF : ∀ x, 0 ≤ F x)
    (n : ℕ) (t : BinaryTree α) : 0 ≤ goodThroughScore G F n t := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact add_nonneg (goodDepthSum_nonnegative G F hF n t) ih

theorem goodThroughScore_split (G : α → Bool) (F : α → ℝ) (n : ℕ) (v : α) (l r : BinaryTree α)
    (hv : G v = true) :
    goodThroughScore G F (n+1) (.node v l r) = F v+goodThroughScore G F n l+goodThroughScore G F n r := by
  induction n with
  | zero => simp [goodThroughScore,goodDepthSum,goodDepthNodes,hv]
  | succ n ih =>
    simp only [goodThroughScore,goodDepthSum,goodDepthNodes,hv,↓reduceIte,List.map_append,List.sum_append]
    simp only [goodThroughScore,goodDepthSum] at ih
    linear_combination ih

/-- A failed complete good subtree has a shortest path to a good
parent missing a good child. No selected descendant is counted more
than once at a prescribed depth. -/
theorem incomplete_good_tree_charge (G : α → Bool) (M : α → ℝ) (hM : ∀ x, 0 ≤ M x)
    (n : ℕ) (t : BinaryTree α) (hC : GoodMissingCharge G M t)
    (hg : rootGood G t = true) (hfail : ¬ GoodThrough G (n+2) t) :
    1 ≤ goodThroughScore G M (n+1) t := by
  induction n generalizing t with
  | zero =>
    cases t with
    | nil => simp [rootGood] at hg
    | node v l r =>
      have hbad : ¬ (rootGood G l = true ∧ rootGood G r = true) := by
        intro hh
        apply hfail
        refine ⟨hg,?_,?_⟩
        · cases l <;> simp_all [GoodThrough,rootGood]
        · cases r <;> simp_all [GoodThrough,rootGood]
      have hm := hC.1 hg hbad
      simpa only [goodThroughScore,goodDepthSum,goodDepthNodes,show G v = true from hg,↓reduceIte,
        List.map_singleton,List.sum_singleton,add_zero] using hm
  | succ n ih =>
    cases t with
    | nil => simp [rootGood] at hg
    | node v l r =>
      have hv : G v = true := hg
      rw [goodThroughScore_split G M (n+1) v l r hv]
      by_cases hbad : ¬ (rootGood G l = true ∧ rootGood G r = true)
      · have hm := hC.1 hv hbad
        linarith only [hm,goodThroughScore_nonnegative G M hM (n+1) l,goodThroughScore_nonnegative G M hM (n+1) r]
      · have hchildren := not_not.mp hbad
        have hFailure : ¬ GoodThrough G (n+2) l ∨ ¬ GoodThrough G (n+2) r := by
          by_contra hh
          push_neg at hh
          exact hfail ⟨hg,hh.1,hh.2⟩
        rcases hFailure with hl | hr
        · have hLeft := ih l hC.2.1 hchildren.1 hl
          linarith only [hLeft,hM v,goodThroughScore_nonnegative G M hM (n+1) r]
        · have hRight := ih r hC.2.2 hchildren.2 hr
          linarith only [hRight,hM v,goodThroughScore_nonnegative G M hM (n+1) l]

end
end StrongSilver.BinaryForest
