-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.DepthPrefixPartition

namespace StrongSilver.BinaryForest
open Real
noncomputable section
variable {α : Type*}
set_option maxHeartbeats 7200000
local instance depthHeightWindowDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Replacing a height window by the first k good levels costs only
original signed charges in a strip of width k*epsilon at its boundary.
Deeper vertices may be bad: their good ancestor at level k suffices. -/
theorem depth_height_window_upper (G : α → Bool) (H F : α → ℝ) (active : α → Prop)
    (ω ε y : ℝ) (k : ℕ) (t : BinaryTree α)
    (hω : 0 ≤ ω) (hε : 0 ≤ ε) (hg : GoodThrough G (k+1) t)
    (he : GoodEdgeDeviation G H ω ε t) (ho : ActiveRootOrder active H t)
    (hActive : ∀ b, G b = true → active b)
    (hylo : rootHeight H t ≤ y) (hyhi : y-rootHeight H t ≤ ω+ε) :
    ((labels t).map fun b => if active b ∧ y-(k:ℝ)*ω < H b ∧ H b ≤ y then F b else 0).sum ≤
      ((depthPrefixLabels k t).map F).sum+
        ((labels t).map fun b => if active b ∧ |y-H b-(k:ℝ)*ω| ≤ (k:ℝ)*ε then |F b| else 0).sum := by
  classical
  let W := fun b : α => if active b ∧ y-(k:ℝ)*ω < H b ∧ H b ≤ y then F b else 0
  let E := fun b : α => if active b ∧ |y-H b-(k:ℝ)*ω| ≤ (k:ℝ)*ε then |F b| else 0
  have hE (b : α) : 0 ≤ E b := by dsimp only [E]; split_ifs; exact abs_nonneg _; exact le_rfl
  cases k with
  | zero =>
    have hW : W = fun _ => 0 := by
      funext b
      dsimp only [W]
      apply if_neg
      rintro ⟨_,h1,h2⟩
      norm_num at h1
      exact (not_lt_of_ge h2) h1
    change ((labels t).map W).sum ≤ ((depthPrefixLabels 0 t).map F).sum+((labels t).map E).sum
    rw [hW]
    simp only [List.map_const',List.sum_replicate,smul_zero,depthPrefixLabels,List.map_nil,List.sum_nil,zero_add]
    exact List.sum_nonneg (by intro x hx; obtain ⟨b,_,rfl⟩ := List.mem_map.mp hx; exact hE b)
  | succ n =>
    cases t with
    | nil => exact False.elim hg
    | node v l r =>
      have hRoot : rootHeight H (BinaryTree.node v l r) = H v := rfl
      have hGoodPrefix : GoodThrough G (n+1) (BinaryTree.node v l r) := goodThrough_prefix (k:=1) hg
      have hDom (b : α) (hb : b ∈ labels (BinaryTree.node v l r)) (ha : active b) : H b ≤ y :=
        (ho.1 b hb ha).trans hylo
      have hPre : ∀ b ∈ depthPrefixLabels (n+1) (BinaryTree.node v l r), W b ≤ F b+E b := by
        intro b hb
        have hG := depthPrefixLabels_good G (n+1) _ hGoodPrefix hb
        have hA := hActive b hG
        have hUpper := hDom b (depthPrefixLabels_mem _ _ hb) hA
        have hLower := good_prefix_height_lower G H ω ε n _ hGoodPrefix he (add_nonneg hω hε) hb
        have hRange : y-H b ≤ ((n+1:ℕ):ℝ)*(ω+ε) := by
          push_cast
          linear_combination hyhi+hLower
        by_cases hw : active b ∧ y-((n+1:ℕ):ℝ)*ω < H b ∧ H b ≤ y
        · dsimp only [W]
          rw [if_pos hw]
          exact le_add_of_nonneg_right (hE b)
        · have hLow : H b ≤ y-((n+1:ℕ):ℝ)*ω := by
            by_contra hn
            exact hw ⟨hA,lt_of_not_ge hn,hUpper⟩
          have hStrip : |y-H b-((n+1:ℕ):ℝ)*ω| ≤ ((n+1:ℕ):ℝ)*ε := by
            apply abs_le.mpr
            constructor
            · have hh := mul_nonneg (Nat.cast_nonneg (n+1)) hε
              linarith only [hLow,hh]
            · nlinarith only [hRange]
          dsimp only [W,E]
          rw [if_neg hw,if_pos (And.intro hA hStrip)]
          linarith only [neg_le_abs (F b)]
      have hRem : ∀ b ∈ depthRemainderLabels (n+1) (BinaryTree.node v l r), W b ≤ E b := by
        intro b hb
        by_cases hw : active b ∧ y-((n+1:ℕ):ℝ)*ω < H b ∧ H b ≤ y
        · have hDepth := good_remainder_height_upper G H active ω ε (n+1) _ hg he ho hb hw.1
          have hStrip : |y-H b-((n+1:ℕ):ℝ)*ω| ≤ ((n+1:ℕ):ℝ)*ε := by
            apply abs_le.mpr
            constructor
            · nlinarith only [hDepth,hylo]
            · have hh := mul_nonneg (Nat.cast_nonneg (n+1)) hε
              linarith only [hw.2.1,hh]
          dsimp only [W,E]
          rw [if_pos hw,if_pos (And.intro hw.1 hStrip)]
          exact le_abs_self _
        · dsimp only [W]
          rw [if_neg hw]
          exact hE b
      have hP := List.sum_le_sum hPre
      rw [List.sum_map_add] at hP
      have hR := List.sum_le_sum hRem
      have hWP := depth_partition_sum (n+1) (BinaryTree.node v l r) W
      have hEP := depth_partition_sum (n+1) (BinaryTree.node v l r) E
      change ((labels (BinaryTree.node v l r)).map W).sum ≤
        ((depthPrefixLabels (n+1) (BinaryTree.node v l r)).map F).sum+((labels (BinaryTree.node v l r)).map E).sum
      linear_combination hP+hR-hWP+hEP

end
end StrongSilver.BinaryForest
