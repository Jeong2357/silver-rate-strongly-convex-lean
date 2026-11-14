-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PaddedSplitCharges

namespace StrongSilver.PaddedSplitInput
open Scalar.SignedIntervals
noncomputable section
set_option maxHeartbeats 2800000

local instance (S : PaddedSplitInput) (δ : ℝ) : Decidable (S.Balanced δ) := Classical.propDecidable _

/-- Summed vertex charges in (4.11), with actual scalar excesses and
without identifying repeated occurrences in the forest. -/
theorem finite_vertex_charges : ∃ c₁ > 0, ∃ c₂ > 0, ∃ C > 0,
    ∀ inputs : List PaddedSplitInput, ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
    c₁*δ^2*(inputs.map fun S => if S.Balanced δ then 0 else S.weight).sum ≤ (inputs.map excess).sum ∧
    c₂*(inputs.map fun S => if S.Balanced δ then S.weight*(drawdown S.left/S.t) else 0).sum ≤ (inputs.map excess).sum ∧
    (inputs.map fun S => S.weight*|S.gain|).sum ≤ C*(inputs.map weight).sum+C*(inputs.map excess).sum := by
  classical
  obtain ⟨c₁,hc₁,hbad⟩ := unbalanced_excess_charge
  obtain ⟨c₂,hc₂,hdraw⟩ := drawdown_excess_charge
  obtain ⟨C,hC,hgain⟩ := weighted_gain_charge
  refine ⟨c₁,hc₁,c₂,hc₂,C,hC,?_⟩
  intro inputs δ hδ hδ1
  induction inputs with
  | nil => simp
  | cons S ss ih =>
    have hb : c₁*δ^2*(if S.Balanced δ then 0 else S.weight) ≤ S.excess := by
      by_cases hS : S.Balanced δ
      · rw [if_pos hS,mul_zero]
        exact S.excess_nonnegative
      · rw [if_neg hS]
        have hh := hbad S δ hδ hδ1 hS
        nlinarith only [hh]
    have hd : c₂*(if S.Balanced δ then S.weight*(drawdown S.left/S.t) else 0) ≤ S.excess := by
      by_cases hS : S.Balanced δ
      · rw [if_pos hS]
        simpa only [mul_assoc] using hdraw S (hS.2.2.trans hδ1)
      · rw [if_neg hS,mul_zero]
        exact S.excess_nonnegative
    have hg := hgain S
    simp only [List.map_cons,List.sum_cons]
    exact ⟨by linear_combination hb+ih.1,by linear_combination hd+ih.2.1,by linear_combination hg+ih.2.2⟩

/-- Failure of the good-vertex negative-mass test splits into the two
charges used by the visibility argument. -/
theorem negative_mass_failure {S : PaddedSplitInput} {δ : ℝ}
    (hbad : δ*S.t < negativeMass S.left) :
    δ*S.t/2 < drawdown S.left ∨ δ*S.t/2 < positiveMass S.left-prefixMax S.left := by
  have hid := negativeMass_identity S.left
  by_contra hn
  push_neg at hn
  linarith only [hbad,hid,hn.1,hn.2]

end
end StrongSilver.PaddedSplitInput
