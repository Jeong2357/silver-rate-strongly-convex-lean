-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandGoodNegativeMass
import StrongSilver.BandCandidateScale

namespace StrongSilver
open ScheduleTree BinaryForest Scalar.SignedIntervals Real Filter Set
noncomputable section
set_option maxHeartbeats 6400000

def bandLocalUpperScale (u A : ℝ) : ℝ := 4*A*u^((1:ℝ)/200)
def bandLocalNegativeScale (u A : ℝ) : ℝ := 8*A*u^(-(19:ℝ)/200)

/-- Actual following pivots and signed gap masses satisfy the common
upper budgets of the two-gap construction, for gamma=1/100. -/
theorem eventually_band_candidate_upper_scales : ∀ᶠ u : ℝ in atTop,
    ∀ κ B μ y : ℝ, ∀ h : List ℝ, ∀ q : LinkedGap,
    0 ≤ κ → 1 < B → u ≤ firstAverageLogScale B → 0 < μ → μ*B ≤ 1/2 →
    y ∈ Icc (outerBandLow u) (outerBandHigh u) →
    q ∈ linkedFrontier (cappedStep μ B) (bandPad u+Real.exp y) 0 κ none none (cartesian h) →
    BandRootCandidate B μ u (Real.log u/200) q y →
    ∃ p : ScheduleNode, q.following = some p ∧ 0 < p.pivot ∧ p.pivot ≤ B ∧
      cappedStep μ B p.pivot ≤ bandLocalUpperScale u (bandCutoff μ u y) ∧
      p.pivot ≤ bandLocalUpperScale u (bandCutoff μ u y) ∧
      negativeMass q.node.source.word ≤ bandLocalNegativeScale u (bandCutoff μ u y) := by
  filter_upwards [eventually_band_candidate_gap_negative_mass,eventually_outer_band_log_window,
    eventually_band_pad_small,eventually_eligible_band_step_upper,eventually_ge_atTop (1:ℝ)]
    with u hNeg hWindow hPad hEligible hu
  intro κ B μ y h q hκ hB hU hμ hμB hy hq hCandidate
  let A := bandCutoff μ u y
  let P := bandPad u
  have hu0 := zero_lt_one.trans_le hu
  have hPow : (1:ℝ) ≤ u^((1:ℝ)/200) := Real.one_le_rpow hu (by norm_num)
  have hδ : 0 ≤ bandTolerance u := (Real.rpow_pos_of_pos hu0 _).le
  obtain ⟨p,hp,hNegative,hUpper⟩ := hNeg κ B μ y (Real.log u/200) h q hκ hB hU hμ hμB hq hCandidate
  obtain ⟨p',hp',hGood',_⟩ := hCandidate.2
  have hEq : p' = p := Option.some.inj (hp'.symm.trans hp)
  have hGood : bandGoodBool B μ u p = true := hEq ▸ hGood'
  have hPred := ((bandGoodBool_iff B μ u p).mp hGood).2
  have hpB := hEligible B μ p.pivot p.pivotIndex hB hU hμ hμB (bandProtectedPredicate_eligible hPred)
  have hStrict := cappedStep_strictMono (B:=B) hμ (by linarith only [hμB])
  have hZero : cappedStep μ B 0 = 0 := by simp only [cappedStep,if_pos (zero_lt_one.trans hB).le,logarithmicStep_zero]
  have hp0 : 0 < p.pivot := hStrict.lt_iff_lt.mp (by rw [hZero]; exact (Real.exp_pos _).trans hPred.1)
  have W := hWindow B μ y hB hU hμ hμB hy
  have hSize := logarithmicCutoff_size hμ (show (0:ℝ) ≤ P by exact (Real.exp_pos _).le) W.2.1
  have hP : 0 < P := Real.exp_pos _
  have hHeight : Real.exp y ≤ 2*A := by dsimp only [A,bandCutoff]; linarith only [hSize.1,hP]
  have hPexp : P ≤ Real.exp y := by
    have hh := (hPad.2 y hy.1).1
    linarith only [hh,Real.exp_pos y]
  have hExp : Real.exp (y+Real.log u/200) = Real.exp y*u^((1:ℝ)/200) := by
    rw [Real.exp_add,Real.rpow_def_of_pos hu0]
    congr 1
    ring
  rw [hExp] at hUpper
  have hEscale := mul_le_mul_of_nonneg_left hPow (Real.exp_pos y).le
  have hAscale := mul_le_mul_of_nonneg_right hHeight (Real.rpow_pos_of_pos hu0 ((1:ℝ)/200)).le
  have hPhi : cappedStep μ B p.pivot ≤ bandLocalUpperScale u A := by
    unfold bandLocalUpperScale
    dsimp only [P] at hPexp
    linarith only [hUpper,hPexp,hEscale,hAscale]
  have hpU := (cappedStep_ge (B:=B) hμ (by linarith only [hμB]) p.pivot).trans hPhi
  have hNegScale := mul_le_mul_of_nonneg_left hPhi (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hδ)
  have hIdentity : 2*bandTolerance u*bandLocalUpperScale u A = bandLocalNegativeScale u A := by
    unfold bandTolerance bandLocalUpperScale bandLocalNegativeScale
    have hh : u^(-(1:ℝ)/10)*u^((1:ℝ)/200) = u^(-(19:ℝ)/200) := by
      rw [← Real.rpow_add hu0]
      norm_num
    calc
      _ = 8*A*(u^(-(1:ℝ)/10)*u^((1:ℝ)/200)) := by ring
      _ = _ := by rw [hh]
  rw [hIdentity] at hNegScale
  exact ⟨p,hp,hp0,hpB,hPhi,hpU,hNegative.trans hNegScale⟩

end
end StrongSilver
