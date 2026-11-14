-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PaddedTreeInput

namespace StrongSilver.ScheduleTree
noncomputable section
set_option maxHeartbeats 3400000

theorem paddedInput_time (φ : ℝ → ℝ) {P κ : ℝ} (hP : 0 < P) (hκ : 0 ≤ κ) (hzero : φ 0 ≤ 0)
    (t : ScheduleTree) (hroot : P < φ t.rootStep) :
    (paddedInput φ hP hκ hzero t hroot).t = φ t.rootStep-P := by
  cases t with
  | leaf hw => exact False.elim (not_lt_of_ge (hzero.trans hP.le) hroot)
  | split l b r => rfl

/-- Padded spacing along an actual left-child edge. The child receives
zero terminal reserve, exactly as in the finite cut identities. -/
theorem padded_balanced_left_spacing {φ : ℝ → ℝ} {P κ δ b : ℝ} {l r : ScheduleTree}
    (hP : 0 < P) (hκ : 0 ≤ κ) (hzero : φ 0 ≤ 0) (hδ : 0 ≤ δ) (hδmax : δ ≤ 1/100)
    (hp : PaddedBalanced φ P κ δ (.split l b r)) (hc : PaddedBalanced φ P 0 δ l) :
    |Real.log (φ b-P)-Real.log (φ l.rootStep-P)-Real.log rho| ≤ 11*δ := by
  let parent := paddedInput φ hP hκ hzero (.split l b r) hp.root_positive
  let child := paddedInput φ hP (show (0:ℝ) ≤ 0 by rfl) hzero l hc.root_positive
  have hparent : parent.Balanced δ := (paddedInput_balance_iff φ hP hκ hzero _ _ δ).mpr hp
  have hchild : child.Balanced δ := (paddedInput_balance_iff φ hP (show (0:ℝ) ≤ 0 by rfl) hzero _ _ δ).mpr hc
  have hmass : child.z = parent.a := by
    rw [paddedInput_mass]
    change gapPrefix φ l.word+P+0 = gapPrefix φ l.word+P
    ring
  have hh := PaddedSplitInput.balanced_edge_log_spacing hδ hδmax hparent hchild (Or.inl hmass)
  rw [paddedInput_time,paddedInput_time] at hh
  exact hh

theorem padded_balanced_right_spacing {φ : ℝ → ℝ} {P κ δ b : ℝ} {l r : ScheduleTree}
    (hP : 0 < P) (hκ : 0 ≤ κ) (hzero : φ 0 ≤ 0) (hδ : 0 ≤ δ) (hδmax : δ ≤ 1/100)
    (hp : PaddedBalanced φ P κ δ (.split l b r)) (hc : PaddedBalanced φ P κ δ r) :
    |Real.log (φ b-P)-Real.log (φ r.rootStep-P)-Real.log rho| ≤ 11*δ := by
  let parent := paddedInput φ hP hκ hzero (.split l b r) hp.root_positive
  let child := paddedInput φ hP hκ hzero r hc.root_positive
  have hparent : parent.Balanced δ := (paddedInput_balance_iff φ hP hκ hzero _ _ δ).mpr hp
  have hchild : child.Balanced δ := (paddedInput_balance_iff φ hP hκ hzero _ _ δ).mpr hc
  have hmass : child.z = parent.b := by
    rw [paddedInput_mass]
    rfl
  have hh := PaddedSplitInput.balanced_edge_log_spacing hδ hδmax hparent hchild (Or.inr hmass)
  rw [paddedInput_time,paddedInput_time] at hh
  exact hh

end
end StrongSilver.ScheduleTree
