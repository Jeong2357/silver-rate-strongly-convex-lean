-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PaddedTreeUnitGain
import StrongSilver.TreeRootOrder

namespace StrongSilver
open ScheduleTree Scalar.SignedIntervals
noncomputable section
set_option maxHeartbeats 3000000

theorem gapPrefix_zero_of_nonpositive (φ : ℝ → ℝ) (word : List ℝ)
    (hh : ∀ b ∈ word, φ b ≤ 0) : gapPrefix φ word = 0 := by
  induction word with
  | nil => rfl
  | cons b word ih =>
    have hb := hh b (by simp)
    have ht := ih (fun a ha => hh a (List.mem_cons_of_mem b ha))
    change max 0 (φ b+gapPrefix φ word) = 0
    rw [ht,add_zero,max_eq_left hb]

/-- In a balanced nonterminal split with small pad both child
intervals contain an actual positive splitting pivot. -/
theorem padded_balanced_children_internal {φ : ℝ → ℝ} {P δ b : ℝ} {l r : ScheduleTree}
    (hφ : Monotone φ) (hP : 0 < P) (hzero : φ 0 ≤ 0) (hδ : 0 ≤ δ) (hδmax : δ ≤ 1/4)
    (hc : (.split l b r : ScheduleTree).Cartesian) (hsmall : P < φ b-P)
    (hb : PaddedBalanced φ P 0 δ (.split l b r)) :
    (∃ ll lr : ScheduleTree, ∃ lb : ℝ, l = .split ll lb lr) ∧
      (∃ rl rr : ScheduleTree, ∃ rb : ℝ, r = .split rl rb rr) := by
  let S := paddedInput φ hP (le_refl (0:ℝ)) hzero (.split l b r) hb.root_positive
  have hbal : S.Balanced δ := (paddedInput_balance_iff φ hP (le_refl (0:ℝ)) hzero _ _ δ).mpr hb
  have hm := PaddedSplitInput.balanced_mass_bounds hδ hδmax hbal
  have hL : φ b-P ≤ gapPrefix φ l.word+P := hm.1
  have hR : φ b-P ≤ gapPrefix φ r.word+P := by simpa only [S,paddedInput,PaddedSplitInput.t,PaddedSplitInput.b,gapPrefix,add_zero] using hm.2.2.1
  constructor
  · cases l with
    | leaf hw =>
      have hz := gapPrefix_zero_of_nonpositive φ hw (fun a ha => (hφ (hc.1 a ha)).trans hzero)
      rw [word,hz,zero_add] at hL
      linarith only [hL,hsmall]
    | split ll lb lr => exact ⟨ll,lr,lb,rfl⟩
  · cases r with
    | leaf hw =>
      have hz := gapPrefix_zero_of_nonpositive φ hw (fun a ha => (hφ (hc.2.1 a ha)).trans hzero)
      rw [word,hz,zero_add] at hR
      linarith only [hR,hsmall]
    | split rl rb rr => exact ⟨rl,rr,rb,rfl⟩

end
end StrongSilver
