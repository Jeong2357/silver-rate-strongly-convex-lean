-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.GoodDepthTransport
import StrongSilver.LabeledWindowForest

namespace StrongSilver.BinaryForest
noncomputable section
variable {α : Type*}
set_option maxHeartbeats 5600000

/-- Two-sided spacing on every edge whose endpoints are good. -/
def GoodEdgeDeviation (G : α → Bool) (H : α → ℝ) (ω ε : ℝ) : BinaryTree α → Prop
  | .nil => True
  | t@(.node _ l r) => GoodEdgeDeviation G H ω ε l ∧ GoodEdgeDeviation G H ω ε r ∧
      (rootGood G t = true → rootGood G l = true → |rootHeight H t-rootHeight H l-ω| ≤ ε) ∧
      (rootGood G t = true → rootGood G r = true → |rootHeight H t-rootHeight H r-ω| ≤ ε)

theorem goodDepthNodes_root_good (G : α → Bool) (j : ℕ) (t : BinaryTree α) {v : α}
    (hv : v ∈ goodDepthNodes G j t) : rootGood G t = true := by
  cases t with
  | nil => simp [goodDepthNodes] at hv
  | node w l r =>
    by_cases hw : G w = true
    · exact hw
    · cases j <;> simp [goodDepthNodes,hw] at hv

theorem goodDepthNodes_mem_labels (G : α → Bool) (j : ℕ) (t : BinaryTree α) {v : α}
    (hv : v ∈ goodDepthNodes G j t) : v ∈ labels t := by
  induction j generalizing t with
  | zero =>
    cases t with
    | nil => simp [goodDepthNodes] at hv
    | node w l r =>
      have hw := goodDepthNodes_root_good G 0 (.node w l r) hv
      simp only [goodDepthNodes,show G w = true from hw,↓reduceIte,List.mem_singleton] at hv
      subst v
      exact List.mem_cons_self
  | succ j ih =>
    cases t with
    | nil => simp [goodDepthNodes] at hv
    | node w l r =>
      have hw := goodDepthNodes_root_good G (j+1) (.node w l r) hv
      simp only [goodDepthNodes,show G w = true from hw,↓reduceIte,List.mem_append] at hv
      rcases hv with hv | hv
      · exact List.mem_cons_of_mem w (List.mem_append_left _ (ih l hv))
      · exact List.mem_cons_of_mem w (List.mem_append_right _ (ih r hv))

/-- Accumulation of the actual edge-spacing errors along a good path. -/
theorem goodDepth_height_deviation (G : α → Bool) (H : α → ℝ) (ω ε : ℝ)
    (j : ℕ) (t : BinaryTree α) (he : GoodEdgeDeviation G H ω ε t) {v : α}
    (hv : v ∈ goodDepthNodes G j t) :
    |rootHeight H t-H v-(j:ℝ)*ω| ≤ (j:ℝ)*ε := by
  induction j generalizing t with
  | zero =>
    cases t with
    | nil => simp [goodDepthNodes] at hv
    | node w l r =>
      have hw := goodDepthNodes_root_good G 0 (.node w l r) hv
      simp only [goodDepthNodes,show G w = true from hw,↓reduceIte,List.mem_singleton] at hv
      subst v
      simp only [rootHeight,Nat.cast_zero,zero_mul,sub_self,sub_zero,abs_zero,le_refl]
  | succ j ih =>
    cases t with
    | nil => simp [goodDepthNodes] at hv
    | node w l r =>
      have hw := goodDepthNodes_root_good G (j+1) (.node w l r) hv
      simp only [goodDepthNodes,show G w = true from hw,↓reduceIte,List.mem_append] at hv
      have hstep (s : BinaryTree α) (hs : v ∈ goodDepthNodes G j s)
          (hS : GoodEdgeDeviation G H ω ε s)
          (hEdge : |H w-rootHeight H s-ω| ≤ ε) :
          |H w-H v-((j+1:ℕ):ℝ)*ω| ≤ ((j+1:ℕ):ℝ)*ε := by
        have htail := ih s hS hs
        calc
          _ = |(H w-rootHeight H s-ω)+(rootHeight H s-H v-(j:ℝ)*ω)| := by congr 1; push_cast; ring
          _ ≤ |H w-rootHeight H s-ω|+|rootHeight H s-H v-(j:ℝ)*ω| := abs_add_le _ _
          _ ≤ ε+(j:ℝ)*ε := add_le_add hEdge htail
          _ = ((j+1:ℕ):ℝ)*ε := by push_cast; ring
      rcases hv with hv | hv
      · exact hstep l hv he.1 (he.2.2.1 hw (goodDepthNodes_root_good G j l hv))
      · exact hstep r hv he.2.1 (he.2.2.2 hw (goodDepthNodes_root_good G j r hv))

end
end StrongSilver.BinaryForest
