-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.LinkedGoodDepth

namespace StrongSilver.BinaryForest
noncomputable section
variable {α : Type*}
set_option maxHeartbeats 4800000

def depthPrefixLabels : ℕ → BinaryTree α → List α
  | 0,_ => []
  | _+1,.nil => []
  | n+1,.node v l r => v::(depthPrefixLabels n l++depthPrefixLabels n r)

def depthRemainderLabels : ℕ → BinaryTree α → List α
  | 0,t => labels t
  | _+1,.nil => []
  | n+1,.node _ l r => depthRemainderLabels n l++depthRemainderLabels n r

theorem depth_partition_sum (n : ℕ) (t : BinaryTree α) (F : α → ℝ) :
    ((depthPrefixLabels n t).map F).sum+((depthRemainderLabels n t).map F).sum = ((labels t).map F).sum := by
  induction n generalizing t with
  | zero => simp [depthPrefixLabels,depthRemainderLabels]
  | succ n ih =>
    cases t with
    | nil => simp [depthPrefixLabels,depthRemainderLabels,labels]
    | node v l r =>
      simp only [depthPrefixLabels,depthRemainderLabels,labels,List.map_cons,List.map_append,List.sum_cons,List.sum_append]
      linear_combination ih l+ih r

theorem depthPrefixLabels_mem (n : ℕ) (t : BinaryTree α) {v : α} (hv : v ∈ depthPrefixLabels n t) : v ∈ labels t := by
  induction n generalizing t with
  | zero => simp [depthPrefixLabels] at hv
  | succ n ih =>
    cases t with
    | nil => simp [depthPrefixLabels] at hv
    | node w l r =>
      simp only [depthPrefixLabels,List.mem_cons,List.mem_append] at hv
      rcases hv with rfl | hl | hr
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_append_left _ (ih l hl))
      · exact List.mem_cons_of_mem _ (List.mem_append_right _ (ih r hr))

theorem depthPrefixLabels_good (G : α → Bool) (n : ℕ) (t : BinaryTree α) (hg : GoodThrough G n t)
    {v : α} (hv : v ∈ depthPrefixLabels n t) : G v = true := by
  induction n generalizing t with
  | zero => simp [depthPrefixLabels] at hv
  | succ n ih =>
    cases t with
    | nil => exact False.elim hg
    | node w l r =>
      simp only [depthPrefixLabels,List.mem_cons,List.mem_append] at hv
      rcases hv with rfl | hl | hr
      · exact hg.1
      · exact ih l hg.2.1 hl
      · exact ih r hg.2.2 hr

def ActiveRootOrder (active : α → Prop) (H : α → ℝ) : BinaryTree α → Prop
  | .nil => True
  | t@(.node v l r) => (∀ b ∈ labels t, active b → H b ≤ H v) ∧ ActiveRootOrder active H l ∧ ActiveRootOrder active H r

/-- The first n+1 good levels stay within n controlled edge lengths
of the actual source root. -/
theorem good_prefix_height_lower (G : α → Bool) (H : α → ℝ) (ω ε : ℝ)
    (n : ℕ) (t : BinaryTree α) (hg : GoodThrough G (n+1) t)
    (he : GoodEdgeDeviation G H ω ε t) (hstep : 0 ≤ ω+ε) {b : α}
    (hb : b ∈ depthPrefixLabels (n+1) t) : rootHeight H t-H b ≤ (n:ℝ)*(ω+ε) := by
  induction n generalizing t with
  | zero =>
    cases t with
    | nil => exact False.elim hg
    | node v l r =>
      simp only [depthPrefixLabels,List.append_nil,List.mem_cons,List.not_mem_nil,or_false] at hb
      subst b
      simp [rootHeight]
  | succ n ih =>
    cases t with
    | nil => exact False.elim hg
    | node v l r =>
      simp only [depthPrefixLabels,List.mem_cons,List.mem_append] at hb
      rcases hb with rfl | hl | hr
      · exact (by simpa only [rootHeight,sub_self] using mul_nonneg (Nat.cast_nonneg (n+1)) hstep)
      · have hi := ih l hg.2.1 he.1 hl
        have hChild : rootGood G l = true := by
          cases l with
          | nil => exact False.elim hg.2.1
          | node w ll lr => exact hg.2.1.1
        have hEdge := (abs_le.mp (he.2.2.1 hg.1 hChild)).2
        change H v-rootHeight H l-ω ≤ ε at hEdge
        change H v-H b ≤ ((n+1:ℕ):ℝ)*(ω+ε)
        push_cast
        linear_combination hi+hEdge
      · have hi := ih r hg.2.2 he.2.1 hr
        have hChild : rootGood G r = true := by
          cases r with
          | nil => exact False.elim hg.2.2
          | node w rl rr => exact hg.2.2.1
        have hEdge := (abs_le.mp (he.2.2.2 hg.1 hChild)).2
        change H v-rootHeight H r-ω ≤ ε at hEdge
        change H v-H b ≤ ((n+1:ℕ):ℝ)*(ω+ε)
        push_cast
        linear_combination hi+hEdge

/-- Below level k, every active descendant lies below its good
ancestor at level k, including descendants outside the good subtree. -/
theorem good_remainder_height_upper (G : α → Bool) (H : α → ℝ) (active : α → Prop) (ω ε : ℝ)
    (k : ℕ) (t : BinaryTree α) (hg : GoodThrough G (k+1) t)
    (he : GoodEdgeDeviation G H ω ε t) (ho : ActiveRootOrder active H t) {b : α}
    (hb : b ∈ depthRemainderLabels k t) (ha : active b) : H b ≤ rootHeight H t-(k:ℝ)*(ω-ε) := by
  induction k generalizing t with
  | zero =>
    cases t with
    | nil => simp [depthRemainderLabels,labels] at hb
    | node v l r => simpa only [rootHeight,Nat.cast_zero,zero_mul,sub_zero] using ho.1 b hb ha
  | succ k ih =>
    cases t with
    | nil => exact False.elim hg
    | node v l r =>
      simp only [depthRemainderLabels,List.mem_append] at hb
      rcases hb with hl | hr
      · have hi := ih l hg.2.1 he.1 ho.2.1 hl
        have hChild : rootGood G l = true := by
          cases l with
          | nil => exact False.elim hg.2.1
          | node w ll lr => exact hg.2.1.1
        have hEdge := (abs_le.mp (he.2.2.1 hg.1 hChild)).1
        change -ε ≤ H v-rootHeight H l-ω at hEdge
        change H b ≤ H v-((k+1:ℕ):ℝ)*(ω-ε)
        push_cast
        linear_combination hi+hEdge
      · have hi := ih r hg.2.2 he.2.1 ho.2.2 hr
        have hChild : rootGood G r = true := by
          cases r with
          | nil => exact False.elim hg.2.2
          | node w rl rr => exact hg.2.2.1
        have hEdge := (abs_le.mp (he.2.2.2 hg.1 hChild)).1
        change -ε ≤ H v-rootHeight H r-ω at hEdge
        change H b ≤ H v-((k+1:ℕ):ℝ)*(ω-ε)
        push_cast
        linear_combination hi+hEdge

end
end StrongSilver.BinaryForest
