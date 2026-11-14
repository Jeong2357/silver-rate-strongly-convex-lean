-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CartesianDepthFourGroups
import StrongSilver.CappedTransform

namespace StrongSilver.ScheduleTree
noncomputable section
set_option maxHeartbeats 2600000

theorem transformedWord_capped {μ B : ℝ} (t : ScheduleTree) (h : ∀ b ∈ t.word, b ≤ B) :
    t.transformedWord (cappedStep μ B) = t.transformedWord (logarithmicStep μ) := by
  unfold transformedWord
  apply List.map_congr_left
  intro b hb
  exact if_pos (h b hb)

theorem prefixMass_capped {μ B : ℝ} (t : ScheduleTree) (h : ∀ b ∈ t.word, b ≤ B) :
    t.prefixMass (cappedStep μ B) = t.prefixMass (logarithmicStep μ) := by
  unfold prefixMass
  rw [transformedWord_capped t h]

theorem gapDrawdown_capped {μ B : ℝ} (t : ScheduleTree) (h : ∀ b ∈ t.word, b ≤ B) :
    t.gapDrawdown (cappedStep μ B) = t.gapDrawdown (logarithmicStep μ) := by
  unfold gapDrawdown
  rw [transformedWord_capped t h]

namespace FourGapGroup

theorem fourth_word_sublist (G : FourGapGroup) : G.fourth.word.Sublist G.tree.word :=
  (right_word_sublist G.third G.fourth G.rightPivot).trans
    (right_word_sublist G.left G.right G.middlePivot)

/-- The exterior factor in the actual trace is exactly the capped
Cartesian factor used by the global telescoping identity. The following
step itself need not be below B. -/
theorem leadingFactor_eq_terminalFactor {G : FourGapGroup} {μ B b : ℝ}
    (hword : ∀ s ∈ G.tree.word, s ≤ B)
    (hKM : 0 < adjustedExcess (cappedStep μ B) G.left G.middlePivot)
    (hKR : 0 < adjustedExcess (cappedStep μ B) G.third G.rightPivot) :
    G.leadingFactor μ B b = terminalFactor (cappedStep μ B) G.tree b := by
  have hfourth : ∀ s ∈ G.fourth.word, s ≤ B := fun s hs => hword s (G.fourth_word_sublist.subset hs)
  unfold leadingFactor terminalFactor
  rw [G.tree_drawdown_eq_last hKM hKR,prefixMass_capped G.tree hword,gapDrawdown_capped G.fourth hfourth]
  rfl

end FourGapGroup
end
end StrongSilver.ScheduleTree
