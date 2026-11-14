-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.LabeledWindowForest

namespace StrongSilver.BinaryForest
noncomputable section
variable {α : Type*}
set_option maxHeartbeats 3800000

/-- Pruning removes whole subtrees and preserves all remaining labels
and their multiplicities. -/
theorem pruneBottom_labels_sublist (H : α → ℝ) (low : ℝ) (t : BinaryTree α) :
    (labels (pruneBottom H low t)).Sublist (labels t) := by
  induction t with
  | nil => exact List.Sublist.refl _
  | node v l r il ir =>
    by_cases hv : low < H v
    · simp only [pruneBottom,if_pos hv,labels]
      exact List.Sublist.cons_cons v (il.append ir)
    · simp only [pruneBottom,if_neg hv,labels]
      exact List.nil_sublist _

/-- Pruning with an arbitrary root test preserves spacing measured by
a different height function on the retained edges. -/
theorem pruneBottom_edge_spaced {G : α → Bool} {H guard : α → ℝ} {s low : ℝ} {t : BinaryTree α}
    (hEdge : EdgeSpaced G H s t) : EdgeSpaced G H s (pruneBottom guard low t) := by
  induction t with
  | nil => trivial
  | node v l r il ir =>
    by_cases hv : low < guard v
    · rw [pruneBottom,if_pos hv]
      refine ⟨il hEdge.1,ir hEdge.2.1,?_,?_⟩
      · intro hp hc
        cases l with
        | nil => simp [pruneBottom,rootGood] at hc
        | node lv ll lr =>
          by_cases hl : low < guard lv
          · have hh := hEdge.2.2.1 hp (by simpa only [pruneBottom,if_pos hl,rootGood] using hc)
            simpa only [rootHeight,pruneBottom,if_pos hl] using hh
          · simp [pruneBottom,hl,rootGood] at hc
      · intro hp hc
        cases r with
        | nil => simp [pruneBottom,rootGood] at hc
        | node rv rl rr =>
          by_cases hr : low < guard rv
          · have hh := hEdge.2.2.2 hp (by simpa only [pruneBottom,if_pos hr,rootGood] using hc)
            simpa only [rootHeight,pruneBottom,if_pos hr] using hh
          · simp [pruneBottom,hr,rootGood] at hc
    · simp only [pruneBottom,if_neg hv,EdgeSpaced]

theorem labelsBelow_iff (H : α → ℝ) (high : ℝ) (t : BinaryTree α) :
    labelsBelow H high t ↔ ∀ q ∈ labels t, H q ≤ high := by
  induction t with
  | nil => simp [labelsBelow,labels]
  | node v l r il ir => simp only [labelsBelow,labels,List.forall_mem_cons,List.forall_mem_append,il,ir]

end
end StrongSilver.BinaryForest
