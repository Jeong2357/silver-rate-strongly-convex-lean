-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CartesianDepthOriginalBounds
import StrongSilver.CartesianUniformExteriorTime

namespace StrongSilver.ScheduleTree.FourGapGroup
open FourPhase Scalar.SignedIntervals
noncomputable section
set_option maxHeartbeats 3600000

/-- All actual-schedule fields of the group data are consequences of
Cartesian order, balanced transformed masses, one original negative-mass
budget, and uniformly small curvature times the selected steps. -/
theorem group_data_from_original_balance {G : FourGapGroup} {μ T b ε B : ℝ}
    (hTmass : T = G.first.prefixMass (logarithmicStep μ)) (hT : 1000 ≤ T)
    (hμ : 0 < μ) (hμB : μ*B ≤ 1/10000) (hμb : μ*b ≤ 1/10000)
    (hε : 0 ≤ ε) (hc : G.tree.Cartesian) (hword : ∀ s ∈ G.tree.word, s ≤ B)
    (hboundary : ∀ s ∈ G.tree.word, s ≤ b)
    (hL : SilverBalanced (logarithmicStep μ) ε G.left)
    (hR : SilverBalanced (logarithmicStep μ) ε G.right)
    (hM : SilverBalanced (logarithmicStep μ) ε G.tree)
    (hshape : ∀ i, |G.massShape (logarithmicStep μ) T i-reference i| ≤ 1/100)
    (hnegative : negativeMass G.tree.word ≤ T/1000) :
    BalancedGroupData G μ T b ε ∧ 100 ≤ b ∧
      drawdown ((G.gaps 3).map (logarithmicStep μ)) ≤ b/100 := by
  have hTpos : 0 < T := by linarith only [hT]
  have hsteps (s : ℝ) (hs : s ∈ G.tree.word) : μ*s < 1 := by
    have hh := mul_le_mul_of_nonneg_left (hword s hs) hμ.le
    linarith only [hh,hμB]
  have hp := G.internal_pivot_positive hc b (1 : Fin 3)
  change 0 < G.middlePivot at hp
  have hpmem := G.internal_pivot_mem b (1 : Fin 3)
  change G.middlePivot ∈ G.tree.word at hpmem
  have hpμ : μ*G.middlePivot ≤ 1/10000 :=
    (mul_le_mul_of_nonneg_left (hword G.middlePivot hpmem) hμ.le).trans hμB
  have hk := (abs_le.mp (hshape 5)).1
  change -(1/100:ℝ) ≤ adjustedExcess (logarithmicStep μ) G.left G.middlePivot/T-1 at hk
  have hKlower : (99/100:ℝ)*T ≤ adjustedExcess (logarithmicStep μ) G.left G.middlePivot :=
    (le_div_iff₀ hTpos).mp (by linarith only [hk])
  have hdraw := gapDrawdown_nonnegative (logarithmicStep μ) G.left
  have hφlower : (99/100:ℝ)*T ≤ logarithmicStep μ G.middlePivot := by
    dsimp only [adjustedExcess] at hKlower
    linarith only [hKlower,hdraw]
  have hdefect := logarithmicStep_defect hμ (show μ*G.middlePivot ≤ 1/2 by linarith only [hpμ])
  have hmul := mul_le_mul_of_nonneg_right hpμ hp.le
  have hpupper : logarithmicStep μ G.middlePivot ≤ (5001/5000:ℝ)*G.middlePivot := by
    nlinarith only [hdefect,hmul]
  have hpT : (9/10:ℝ)*T ≤ G.middlePivot := by nlinarith only [hφlower,hpupper,hTpos]
  have hpb := hboundary G.middlePivot hpmem
  have hbT : (4/5:ℝ)*T ≤ b := by linarith only [hpT,hpb,hTpos]
  have hb100 : 100 ≤ b := by linarith only [hbT,hT]
  have hgapN (i : Fin 4) : negativeMass (G.gaps i) ≤ T/1000 :=
    (negative_mass_sublist_le (G.gap_word_sublist i)).trans hnegative
  have hgapsteps (i : Fin 4) : ∀ s ∈ G.gaps i, μ*s < 1 :=
    fun s hs => hsteps s ((G.gap_word_sublist i).subset hs)
  have hd := (transformed_drawdown_le_negative_mass hμ (G.gaps 3) (hgapsteps 3)).trans (hgapN 3)
  have hdb100 : drawdown ((G.gaps 3).map (logarithmicStep μ)) ≤ b/100 := by
    linarith only [hd,hbT,hTpos]
  refine ⟨?_,hb100,hdb100⟩
  exact {
    scale_eq := hTmass
    mu_positive := hμ
    scale_lower := by linarith only [hT]
    tolerance_nonnegative := hε
    gap_steps := hgapsteps
    pivot_steps := fun i => ⟨G.internal_pivot_positive hc b i,hsteps _ (G.internal_pivot_mem b i)⟩
    left_balance := hL
    right_balance := hR
    root_balance := hM
    negative_mass := fun i => (hgapN i).trans (by linarith only [hTpos])
    exterior_lower := by linarith only [hb100]
    exterior_scale := hbT
    exterior_drawdown := by linarith only [hdb100,hb100]
    exterior_small := by linarith only [hμb]
  }

end
end StrongSilver.ScheduleTree.FourGapGroup
