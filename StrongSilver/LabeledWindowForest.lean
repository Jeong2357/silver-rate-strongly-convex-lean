-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.LabeledSpacedForest
import StrongSilver.IndexedScheduleTree

namespace StrongSilver.BinaryForest
noncomputable section
variable {α : Type*}
set_option maxHeartbeats 5200000

def rootHeight (H : α → ℝ) : BinaryTree α → ℝ
  | .nil => 0
  | .node v _ _ => H v

def rootGood (G : α → Bool) : BinaryTree α → Bool
  | .nil => false
  | .node v _ _ => G v

/-- Edge spacing stated on the actual labels, before restricting to a
finite height window. -/
def EdgeSpaced (G : α → Bool) (H : α → ℝ) (s : ℝ) : BinaryTree α → Prop
  | .nil => True
  | t@(.node _ l r) => EdgeSpaced G H s l ∧ EdgeSpaced G H s r ∧
      (rootGood G t = true → rootGood G l = true → s ≤ rootHeight H t-rootHeight H l) ∧
      (rootGood G t = true → rootGood G r = true → s ≤ rootHeight H t-rootHeight H r)

def labelsBelow (H : α → ℝ) (high : ℝ) : BinaryTree α → Prop
  | .nil => True
  | .node v l r => H v ≤ high ∧ labelsBelow H high l ∧ labelsBelow H high r

/-- Remove a whole subtree when its root is below the window. On an
ordered tree this is exactly the bottom height truncation, without
contracting edges or altering labels. -/
def pruneBottom (H : α → ℝ) (low : ℝ) : BinaryTree α → BinaryTree α
  | .nil => .nil
  | .node v l r => if low < H v then .node v (pruneBottom H low l) (pruneBottom H low r) else .nil

private theorem good_component_root {G : α → Bool} {t : BinaryTree α}
    (h : 0 < goodComponentHeight (rootGood G) t) : rootGood G t = true := by
  cases t with
  | nil => simp only [goodComponentHeight] at h; omega
  | node v l r =>
    by_contra hn
    have hf := Bool.eq_false_iff.mpr hn
    simp only [goodComponentHeight,hf,Bool.false_eq_true,↓reduceIte] at h
    omega

/-- Bottom truncation preserves the original edge spacing and supplies
all height-window hypotheses needed by the finite good/bad forest bound. -/
theorem pruneBottom_spaced {G : α → Bool} {H : α → ℝ} {s low high : ℝ} {t : BinaryTree α}
    (hEdge : EdgeSpaced G H s t) (hUpper : labelsBelow H high t) :
    SpacedGoodTree (rootGood G) (rootHeight H) s low high (pruneBottom H low t) := by
  induction t with
  | nil => trivial
  | node v l r il ir =>
    by_cases hv : low < H v
    · rw [pruneBottom,if_pos hv]
      refine ⟨hv.le,hUpper.1,il hEdge.1 hUpper.2.1,ir hEdge.2.1 hUpper.2.2,?_,?_⟩
      · intro hparent hchild
        have hgood := good_component_root hchild
        cases l with
        | nil => simp [pruneBottom,goodComponentHeight] at hchild
        | node lv ll lr =>
          by_cases hl : low < H lv
          · simp only [pruneBottom,if_pos hl,rootGood] at hgood
            have hh := hEdge.2.2.1 hparent hgood
            simpa only [rootHeight,pruneBottom,if_pos hl] using hh
          · simp only [pruneBottom,if_neg hl,goodComponentHeight] at hchild
            omega
      · intro hparent hchild
        have hgood := good_component_root hchild
        cases r with
        | nil => simp [pruneBottom,goodComponentHeight] at hchild
        | node rv rl rr =>
          by_cases hr : low < H rv
          · simp only [pruneBottom,if_pos hr,rootGood] at hgood
            have hh := hEdge.2.2.2 hparent hgood
            simpa only [rootHeight,pruneBottom,if_pos hr] using hh
          · simp only [pruneBottom,if_neg hr,goodComponentHeight] at hchild
            omega
    · simp only [pruneBottom,if_neg hv,SpacedGoodTree]

/-- A finite window component in the original labeled tree has the
required binary count bound after all bad vertices are deleted. -/
theorem pruneBottom_node_bound {G : α → Bool} {H : α → ℝ} {s low high : ℝ} {m : ℕ} {t : BinaryTree α}
    (hs : 0 < s) (hwindow : high-low < (m:ℝ)*s)
    (hEdge : EdgeSpaced G H s t) (hUpper : labelsBelow H high t) :
    (pruneBottom H low t).numNodes ≤
      2^(m+1)*(badNodeCount (rootGood G) (pruneBottom H low t)+1) :=
  spaced_forest_node_bound hs hwindow (pruneBottom_spaced hEdge hUpper)

end
end StrongSilver.BinaryForest
