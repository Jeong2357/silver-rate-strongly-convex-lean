-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.LabeledWindowForest
import StrongSilver.ActualScheduleEdges

namespace StrongSilver
open ScheduleTree BinaryForest
noncomputable section
set_option maxHeartbeats 4200000

def nodePaddedHeight (φ : ℝ → ℝ) (P : ℝ) (q : ScheduleNode) : ℝ := nodeHeight φ P (q.source,q.reserve)

def nodeBalancedBool (φ : ℝ → ℝ) (P δ : ℝ) (q : ScheduleNode) : Bool := by
  classical
  exact decide (PaddedBalanced φ P q.reserve δ q.source)

/-- The spacing hypotheses of the labeled good/bad forest theorem
hold on the actual positioned schedule tree, including the exact child
reserve convention. -/
theorem indexedTree_balanced_edge_spaced {φ : ℝ → ℝ} {P κ δ : ℝ}
    (hP : 0 < P) (hκ : 0 ≤ κ) (hzero : φ 0 ≤ 0) (hδ : 0 ≤ δ) (hδmax : δ ≤ 1/100)
    (start : ℕ) (t : ScheduleTree) :
    EdgeSpaced (nodeBalancedBool φ P δ) (nodePaddedHeight φ P) (Real.log rho-11*δ) (indexedTree start κ t) := by
  classical
  induction t generalizing start κ with
  | leaf hw => trivial
  | split l b r il ir =>
    refine ⟨il (le_refl (0:ℝ)) start,ir hκ (start+l.word.length+1),?_,?_⟩
    · intro hp hc
      have hparent : PaddedBalanced φ P κ δ (.split l b r) := of_decide_eq_true hp
      cases l with
      | leaf hw => simp [indexedTree,rootGood] at hc
      | split ll lb lr =>
        have hchild : PaddedBalanced φ P 0 δ (.split ll lb lr) := of_decide_eq_true hc
        have hh := padded_balanced_left_spacing hP hκ hzero hδ hδmax hparent hchild
        change Real.log rho-11*δ ≤ Real.log (φ b-P)-Real.log (φ lb-P)
        simp only [rootStep_split] at hh
        linarith only [(abs_le.mp hh).1]
    · intro hp hc
      have hparent : PaddedBalanced φ P κ δ (.split l b r) := of_decide_eq_true hp
      cases r with
      | leaf hw => simp [indexedTree,rootGood] at hc
      | split rl rb rr =>
        have hchild : PaddedBalanced φ P κ δ (.split rl rb rr) := of_decide_eq_true hc
        have hh := padded_balanced_right_spacing hP hκ hzero hδ hδmax hparent hchild
        change Real.log rho-11*δ ≤ Real.log (φ b-P)-Real.log (φ rb-P)
        simp only [rootStep_split] at hh
        linarith only [(abs_le.mp hh).1]

end
end StrongSilver
