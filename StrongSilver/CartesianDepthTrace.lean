-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CartesianUniformGroupsFromBalance
import StrongSilver.CartesianDepthSequenceReady

namespace StrongSilver.ScheduleTree.FourGapGroup
open Scalar.SignedIntervals
noncomputable section
set_option maxHeartbeats 4800000

/-- Actual finite depth construction for the left gap in Lemma 4.2.
The input consists only of the original Cartesian word, balance and
uniform numeric budgets. All groups, interpolation families, internal
joins and the full finite-dimensional last-iterate witness are built. -/
theorem balanced_depth_trace : ∃ C > 0, ∃ τ > 0, ∃ c > 0,
    ∀ μ B ε L U Zmax η : ℝ, ∀ d : ℕ, ∀ t : ScheduleTree, ∀ b : ℝ,
    0 < μ → 0 ≤ B → μ*B ≤ 1/10000 → μ*b ≤ 1/10000 → 0 ≤ ε →
    ε+μ*t.prefixMass (logarithmicStep μ) ≤ τ →
    t.Cartesian → (∀ s ∈ t.word, s ≤ B) → 0 < b → (∀ s ∈ t.word, s ≤ b) →
    balancedThrough (logarithmicStep μ) ε (d+2) t →
    1000 ≤ L → L ≤ (1/4:ℝ)^(d+2)*t.prefixMass (logarithmicStep μ) → b ≤ U →
    negativeMass t.word ≤ L/1000 → 2*U*negativeMass t.word ≤ c*L^2 →
    0 ≤ η → η ≤ c → 2*U*Zmax ≤ c*L →
    ∀ H Z ηo Mo Go r : ℝ, ∀ h : List ℝ, ∀ W : FourPhaseTrace μ h H Z ηo Mo Go r,
    L ≤ H → H ≤ (9/20:ℝ)*cappedStep μ B b → Z ≤ Zmax →
    ∃ qs : List Group, qs.map (fun q => (q.1.tree,q.2)) = depthPhases d t b ∧
      Nonempty (FourPhaseTrace μ ((t.word++[b])++h) (firstScale μ qs H) 0 η 26
        (1/firstScale μ qs H) (r*sequenceRate C μ B ε η qs Z)) := by
  obtain ⟨C,hC,δ,hδ,c,hc,hsequence⟩ := exists_group_sequence_trace
  obtain ⟨τ,hτ,huniform⟩ := exists_uniform_groups_radius hδ
  refine ⟨C,hC,min τ (1/100),lt_min hτ (by norm_num),c,hc,?_⟩
  intro μ B ε L U Zmax η d t b hμ hB hμB hμb hε hnear hcart hword hb hdom hbal hL hLdepth hbU hN hNbudget
    hη hηc hZbudget H Z ηo Mo Go r h W hHlow hHup hZmax
  obtain ⟨qs,hqs⟩ := exists_depth_four_groups b (balancedThrough_complete hbal)
  have hU := huniform c μ B ε L U d t b qs hμ hB hμB hμb hε
    (hnear.trans (min_le_left _ _)) hcart hword hb hdom hbal hqs hL hLdepth hbU hN hNbudget
  have hcap : μ*B ≤ 1/2 := by linarith only [hμB]
  have hε100 : ε ≤ 1/100 := by
    have hh := mul_nonneg hμ.le (prefixMass_positive (logarithmicStep μ) t).le
    have hb := hnear.trans (min_le_right _ _)
    linarith only [hh,hb]
  have hready := uniform_depth_sequence_ready hcap hε100 (show 0 < L by linarith only [hL])
    (hb.le.trans hbU) hc.le hZbudget d t b qs H Z hqs hbal hword hU hHlow hHup
    W.suffix_bounds.offset_nonnegative hZmax
  obtain ⟨P⟩ := hsequence μ B ε η hB hcap hη hηc qs H Z ηo Mo Go r h W hready
  have hsteps := depth_groups_word hqs
  have hqsne : qs ≠ [] := by
    intro hn
    have hh : depthPhases d t b = [] := by simpa only [hn,List.map_nil] using hqs.symm
    exact depthPhases_ne_nil d t b hh
  refine ⟨qs,hqs,?_⟩
  cases qs with
  | nil => exact False.elim (hqsne rfl)
  | cons q qs =>
    simpa only [firstScale,firstOffset,firstGate,firstPointCap,firstSlopeCap,hsteps] using Nonempty.intro P

end
end StrongSilver.ScheduleTree.FourGapGroup
