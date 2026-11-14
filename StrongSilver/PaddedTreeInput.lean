-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PaddedLogSpacing
import StrongSilver.ReservedTreeNodes

namespace StrongSilver.ScheduleTree
open Scalar.SignedIntervals
noncomputable section
set_option maxHeartbeats 3600000

/-- Balance on an original tree interval, including its transformed
height domain and the terminal reserve assigned to this occurrence. -/
def PaddedBalanced (φ : ℝ → ℝ) (P κ δ : ℝ) : ScheduleTree → Prop
  | .leaf _ => False
  | .split l b r => P < φ b ∧
      |Real.log ((gapPrefix φ l.word+P)/(rho*(φ b-P)))| ≤ δ ∧
      |Real.log ((gapPrefix φ r.word+P+κ)/(rho*(φ b-P)))| ≤ δ ∧ l.gapDrawdown φ/(φ b-P) ≤ δ

def PaddedGood (φ : ℝ → ℝ) (P κ δ : ℝ) : ScheduleTree → Prop
  | .leaf _ => False
  | t@(.split l b _) => PaddedBalanced φ P κ δ t ∧ negativeMass (l.word.map φ) ≤ δ*(φ b-P)

/-- Canonical scalar input for the actual transformed left and right
words. No object is selected merely by matching its gain and weight. -/
def paddedInput (φ : ℝ → ℝ) {P κ : ℝ} (hP : 0 < P) (hκ : 0 ≤ κ) (hzero : φ 0 ≤ 0)
    (t : ScheduleTree) (hroot : P < φ t.rootStep) : PaddedSplitInput := by
  cases t with
  | leaf hw =>
    have hh : P < φ 0 := hroot
    exact False.elim (not_lt_of_ge (hzero.trans hP.le) hh)
  | split l b r =>
    exact ⟨l.word.map φ,r.word.map φ,φ b,P,κ,hP,hκ,hroot⟩

theorem paddedInput_weight (φ : ℝ → ℝ) {P κ : ℝ} (hP : 0 < P) (hκ : 0 ≤ κ) (hzero : φ 0 ≤ 0)
    (t : ScheduleTree) (hroot : P < φ t.rootStep) :
    (paddedInput φ hP hκ hzero t hroot).weight = (φ t.rootStep-P)^nu := by
  cases t with
  | leaf hw => exact False.elim (not_lt_of_ge (hzero.trans hP.le) hroot)
  | split l b r => rfl

theorem paddedInput_gain (φ : ℝ → ℝ) {P κ : ℝ} (hP : 0 < P) (hκ : 0 ≤ κ) (hzero : φ 0 ≤ 0)
    (t : ScheduleTree) (hroot : P < φ t.rootStep) :
    (paddedInput φ hP hκ hzero t hroot).gain = paddedRootGain φ P κ t := by
  cases t with
  | leaf hw => exact False.elim (not_lt_of_ge (hzero.trans hP.le) hroot)
  | split l b r =>
    simp only [paddedInput,PaddedSplitInput.gain,PaddedSplitInput.a,PaddedSplitInput.b,PaddedSplitInput.t,
      PaddedSplitInput.z,paddedRootGain,gapPrefix,List.map_append,List.map_cons]

theorem paddedInput_decrease (φ : ℝ → ℝ) {P κ : ℝ} (hP : 0 < P) (hκ : 0 ≤ κ) (hzero : φ 0 ≤ 0)
    (t : ScheduleTree) (hroot : P < φ t.rootStep) :
    (paddedInput φ hP hκ hzero t hroot).decrease = paddedRootDecrease φ P κ t := by
  cases t with
  | leaf hw => exact False.elim (not_lt_of_ge (hzero.trans hP.le) hroot)
  | split l b r =>
    simp only [paddedInput,PaddedSplitInput.decrease,PaddedSplitInput.a,PaddedSplitInput.b,PaddedSplitInput.z,
      paddedRootDecrease,gapPrefix,List.map_append,List.map_cons]

theorem paddedInput_mass (φ : ℝ → ℝ) {P κ : ℝ} (hP : 0 < P) (hκ : 0 ≤ κ) (hzero : φ 0 ≤ 0)
    (t : ScheduleTree) (hroot : P < φ t.rootStep) :
    (paddedInput φ hP hκ hzero t hroot).z = gapPrefix φ t.word+P+κ := by
  cases t with
  | leaf hw => exact False.elim (not_lt_of_ge (hzero.trans hP.le) hroot)
  | split l b r =>
    simp only [paddedInput,PaddedSplitInput.z,word,gapPrefix,List.map_append,List.map_cons]

theorem paddedInput_balance_iff (φ : ℝ → ℝ) {P κ : ℝ} (hP : 0 < P) (hκ : 0 ≤ κ) (hzero : φ 0 ≤ 0)
    (t : ScheduleTree) (hroot : P < φ t.rootStep) (δ : ℝ) :
    (paddedInput φ hP hκ hzero t hroot).Balanced δ ↔ PaddedBalanced φ P κ δ t := by
  cases t with
  | leaf hw => exact False.elim (not_lt_of_ge (hzero.trans hP.le) hroot)
  | split l b r =>
    change (_ ∧ _ ∧ _) ↔ (P < φ b ∧ _ ∧ _ ∧ _)
    exact ⟨fun h => ⟨hroot,h⟩,fun h => h.2⟩

theorem PaddedBalanced.root_positive {φ : ℝ → ℝ} {P κ δ : ℝ} {t : ScheduleTree}
    (h : PaddedBalanced φ P κ δ t) : P < φ t.rootStep := by
  cases t with
  | leaf hw => exact False.elim h
  | split l b r => exact h.1

end
end StrongSilver.ScheduleTree
