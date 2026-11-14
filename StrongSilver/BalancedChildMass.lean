-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BalancedChildrenInternal
import StrongSilver.ActualScheduleEdges

namespace StrongSilver.PaddedSplitInput
open Scalar.SignedIntervals
noncomputable section
set_option maxHeartbeats 2600000

/-- Both child intervals of a balanced nonterminal split carry a fixed
fraction of the parent's selected time in transformed positive mass. -/
theorem balanced_child_positive_mass {S : PaddedSplitInput} {δ : ℝ}
    (hres : S.reserve = 0) (hsmall : S.pad ≤ S.t/4) (hδ : 0 ≤ δ) (hδmax : δ ≤ 1/4)
    (hb : S.Balanced δ) : S.t/2 ≤ positiveMass S.left ∧ S.t/2 ≤ positiveMass S.right := by
  have hm := balanced_mass_bounds hδ hδmax hb
  have hL := prefixMax_le_positiveMass S.left
  have hR := prefixMax_le_positiveMass S.right
  have ht := S.t_positive
  have hl : S.t ≤ prefixMax S.left+S.pad := hm.1
  have hr : S.t ≤ prefixMax S.right+S.pad := by
    have hh := hm.2.2.1
    change S.t ≤ prefixMax S.right+S.pad+S.reserve at hh
    simpa only [hres,add_zero] using hh
  exact ⟨by linarith only [hL,hl,hsmall,ht],by linarith only [hR,hr,hsmall,ht]⟩

end
end StrongSilver.PaddedSplitInput

namespace StrongSilver
open ScheduleTree Scalar.SignedIntervals
noncomputable section

theorem actual_child_positive_mass {φ : ℝ → ℝ} {P δ : ℝ} {p c : ScheduleNode}
    (he : ScheduleChild p c) (hP : 0 < P) (hzero : φ 0 ≤ 0) (hpRes : p.reserve = 0)
    (hsmall : P ≤ (φ p.pivot-P)/4) (hδ : 0 ≤ δ) (hδmax : δ ≤ 1/4)
    (hb : PaddedBalanced φ P p.reserve δ p.source) :
    (φ p.pivot-P)/2 ≤ positiveMass (c.source.word.map φ) := by
  obtain ⟨l,r,b,hsource,hchild⟩ := he
  rw [hpRes] at hb
  have hb' : PaddedBalanced φ P 0 δ (.split l b r) := hsource ▸ hb
  let S := paddedInput φ hP (le_refl (0:ℝ)) hzero (.split l b r) hb'.root_positive
  have hbal : S.Balanced δ := (paddedInput_balance_iff φ hP (le_refl (0:ℝ)) hzero _ _ δ).mpr hb'
  have hres : S.reserve = 0 := rfl
  have hs : S.pad ≤ S.t/4 := by
    change P ≤ (φ b-P)/4
    simpa only [ScheduleNode.pivot,hsource,rootStep_split] using hsmall
  have hm := PaddedSplitInput.balanced_child_positive_mass hres hs hδ hδmax hbal
  rcases hchild with hl | hr
  · rw [ScheduleNode.pivot,hsource,rootStep_split,hl.1]
    exact hm.1
  · rw [ScheduleNode.pivot,hsource,rootStep_split,hr.1]
    exact hm.2

end
end StrongSilver
