-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CartesianCappedTreeMass

namespace StrongSilver.ScheduleTree
noncomputable section
set_option maxHeartbeats 3000000

theorem adjustedExcess_capped {μ B b : ℝ} (l : ScheduleTree) (hb : b ≤ B)
    (hl : ∀ s ∈ l.word, s ≤ B) :
    adjustedExcess (cappedStep μ B) l b = adjustedExcess (logarithmicStep μ) l b := by
  unfold adjustedExcess
  rw [show cappedStep μ B b = logarithmicStep μ b from if_pos hb,gapDrawdown_capped l hl]

theorem rootGain_capped {μ B : ℝ} (t : ScheduleTree) (h : ∀ s ∈ t.word, s ≤ B) :
    rootGain (cappedStep μ B) t = rootGain (logarithmicStep μ) t := by
  cases t with
  | leaf h => rfl
  | split l b r =>
    have hl : ∀ s ∈ l.word, s ≤ B := fun s hs => h s ((left_word_sublist l r b).subset hs)
    have hr : ∀ s ∈ r.word, s ≤ B := fun s hs => h s ((right_word_sublist l r b).subset hs)
    have hb : b ≤ B := h b (by simp [word])
    change Real.log (adjustedExcess (cappedStep μ B) l b*prefixMass (cappedStep μ B) (.split l b r)/
      (l.prefixMass (cappedStep μ B)*r.prefixMass (cappedStep μ B))) = _
    rw [adjustedExcess_capped l hb hl,prefixMass_capped (.split l b r) h,prefixMass_capped l hl,prefixMass_capped r hr]
    rfl

theorem positiveExcessThrough_capped {μ B : ℝ} {d : ℕ} {t : ScheduleTree}
    (hword : ∀ s ∈ t.word, s ≤ B) (hpos : positiveExcessThrough (logarithmicStep μ) d t) :
    positiveExcessThrough (cappedStep μ B) d t := by
  induction d generalizing t with
  | zero => trivial
  | succ d ih =>
    cases t with
    | leaf h => trivial
    | split l b r =>
      have hl : ∀ s ∈ l.word, s ≤ B := fun s hs => hword s ((left_word_sublist l r b).subset hs)
      have hr : ∀ s ∈ r.word, s ≤ B := fun s hs => hword s ((right_word_sublist l r b).subset hs)
      have hb : b ≤ B := hword b (by simp [word])
      exact ⟨by rw [adjustedExcess_capped l hb hl]; exact hpos.1,ih hl hpos.2.1,ih hr hpos.2.2⟩

theorem levelSum_rootGain_capped {μ B : ℝ} (d : ℕ) (t : ScheduleTree) (hword : ∀ s ∈ t.word, s ≤ B) :
    levelSum (rootGain (cappedStep μ B)) d t = levelSum (rootGain (logarithmicStep μ)) d t := by
  induction d generalizing t with
  | zero => cases t <;> simp only [levelSum,rootGain_capped _ hword]
  | succ d ih =>
    cases t with
    | leaf h => rfl
    | split l b r =>
      exact congrArg₂ (·+·) (ih l (fun s hs => hword s ((left_word_sublist l r b).subset hs)))
        (ih r (fun s hs => hword s ((right_word_sublist l r b).subset hs)))

theorem throughSum_rootGain_capped {μ B : ℝ} (d : ℕ) (t : ScheduleTree) (hword : ∀ s ∈ t.word, s ≤ B) :
    throughSum (rootGain (cappedStep μ B)) d t = throughSum (rootGain (logarithmicStep μ)) d t := by
  induction d generalizing t with
  | zero => rfl
  | succ d ih =>
    cases t with
    | leaf h => rfl
    | split l b r =>
      simp only [throughSum,rootGain_capped _ hword,
        ih l (fun s hs => hword s ((left_word_sublist l r b).subset hs)),
        ih r (fun s hs => hword s ((right_word_sublist l r b).subset hs))]

end
end StrongSilver.ScheduleTree
