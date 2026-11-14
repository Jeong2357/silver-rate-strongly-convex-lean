-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CartesianCappedGain
import StrongSilver.CartesianBalancedScales

namespace StrongSilver.ScheduleTree
noncomputable section
set_option maxHeartbeats 4400000

/-- Below the cap, balance is a property of the same actual signed
word for the capped and uncapped logarithmic transforms. -/
theorem silverBalanced_capped {μ B ε : ℝ} {t : ScheduleTree} (hword : ∀ s ∈ t.word, s ≤ B) :
    SilverBalanced (cappedStep μ B) ε t ↔ SilverBalanced (logarithmicStep μ) ε t := by
  cases t with
  | leaf word => rfl
  | split l b r =>
    have hl : ∀ s ∈ l.word, s ≤ B := fun s hs => hword s ((left_word_sublist l r b).subset hs)
    have hr : ∀ s ∈ r.word, s ≤ B := fun s hs => hword s ((right_word_sublist l r b).subset hs)
    have hb : b ≤ B := hword b (by simp [word])
    simp only [SilverBalanced]
    rw [show cappedStep μ B b = logarithmicStep μ b from if_pos hb,
      prefixMass_capped l hl,prefixMass_capped r hr,adjustedExcess_capped l hb hl]

theorem balancedThrough_capped {μ B ε : ℝ} {d : ℕ} {t : ScheduleTree} (hword : ∀ s ∈ t.word, s ≤ B) :
    balancedThrough (cappedStep μ B) ε d t ↔ balancedThrough (logarithmicStep μ) ε d t := by
  induction d generalizing t with
  | zero => rfl
  | succ d ih =>
    cases t with
    | leaf word => rfl
    | split l b r =>
      have hl : ∀ s ∈ l.word, s ≤ B := fun s hs => hword s ((left_word_sublist l r b).subset hs)
      have hr : ∀ s ∈ r.word, s ≤ B := fun s hs => hword s ((right_word_sublist l r b).subset hs)
      exact and_congr (silverBalanced_capped hword) (and_congr (ih hl) (ih hr))

end
end StrongSilver.ScheduleTree
