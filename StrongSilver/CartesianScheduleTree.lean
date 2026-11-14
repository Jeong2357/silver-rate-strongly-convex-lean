-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FirstMaximumSplit

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 2200000

/-- A signed schedule tree keeps the complete nonpositive words at its
leaves. Internal nodes store the original selected positive step. -/
inductive ScheduleTree where
  | leaf : List ℝ → ScheduleTree
  | split : ScheduleTree → ℝ → ScheduleTree → ScheduleTree

namespace ScheduleTree

def word : ScheduleTree → List ℝ
  | .leaf h => h
  | .split l b r => l.word++b::r.word

def nodeCount : ScheduleTree → ℕ
  | .leaf _ => 0
  | .split l _ r => l.nodeCount+1+r.nodeCount

/-- Strict order on the left implements the earliest-index tie rule. -/
def Cartesian : ScheduleTree → Prop
  | .leaf h => ∀ b ∈ h, b ≤ 0
  | .split l b r => l.Cartesian ∧ r.Cartesian ∧ 0 < b ∧
      (∀ x ∈ l.word, x < b) ∧ (∀ x ∈ r.word, x ≤ b)

theorem exists_cartesian (h : List ℝ) : ∃ t : ScheduleTree, t.Cartesian ∧ t.word = h := by
  have aux (n : ℕ) : ∀ h : List ℝ, h.length = n → ∃ t : ScheduleTree, t.Cartesian ∧ t.word = h := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro h hn
      by_cases hp : ∃ b ∈ h, 0 < b
      · obtain ⟨left,b,right,he,hb,hl,hr⟩ := first_maximum_split h hp
        have hlen : left.length+1+right.length = n := by
          rw [he,List.length_append,List.length_cons] at hn
          omega
        obtain ⟨l,hcl,hwl⟩ := ih left.length (by omega) left rfl
        obtain ⟨r,hcr,hwr⟩ := ih right.length (by omega) right rfl
        refine ⟨.split l b r,⟨hcl,hcr,hb,?_,?_⟩,?_⟩
        · simpa only [hwl] using hl
        · simpa only [hwr] using hr
        · change l.word++b::r.word = h
          rw [hwl,hwr,← he]
      · refine ⟨.leaf h,?_,rfl⟩
        exact fun b hb => le_of_not_gt (fun hbp => hp ⟨b,hb,hbp⟩)
  exact aux h.length h rfl

/-- The number of positive pivots is bounded by the original length. -/
theorem nodeCount_le_length (t : ScheduleTree) : t.nodeCount ≤ t.word.length := by
  induction t with
  | leaf h => simp [nodeCount]
  | split l b r il ir =>
    simp only [nodeCount,word,List.length_append,List.length_cons]
    omega

/-- The entire word below either child is an actual contiguous subword
of its parent, including all negative steps. -/
theorem left_word_sublist (l r : ScheduleTree) (b : ℝ) : l.word.Sublist (ScheduleTree.split l b r).word :=
  List.sublist_append_left _ _

theorem right_word_sublist (l r : ScheduleTree) (b : ℝ) : r.word.Sublist (ScheduleTree.split l b r).word :=
  (List.sublist_cons_self _ _).trans (List.sublist_append_right _ _)

def cartesian (h : List ℝ) : ScheduleTree := Classical.choose (exists_cartesian h)

theorem cartesian_valid (h : List ℝ) : (cartesian h).Cartesian := (Classical.choose_spec (exists_cartesian h)).1

theorem cartesian_word (h : List ℝ) : (cartesian h).word = h := (Classical.choose_spec (exists_cartesian h)).2

end ScheduleTree
end
end StrongSilver
