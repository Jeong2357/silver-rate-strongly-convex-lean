-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandFarChildMass
import StrongSilver.BandBadWeightRate

namespace StrongSilver
open ScheduleTree Real Filter Set
noncomputable section
set_option maxHeartbeats 3400000

/-- The far-child contribution of a unit height bin at width log(u)/2,
with the actual tolerance u^(-1/10), decays as u^(-(1-nu)/2). -/
theorem eventually_band_far_child_rate : ∃ C > 0, ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ j : ℝ, ∀ h : List ℝ,
    1 < B → B ≤ cap → u ≤ firstAverageLogScale B → 0 < μ → μ*B ≤ 1/2 →
    j+1-Real.log u/2 ∈ Icc (outerBandLow u) (outerBandHigh u) →
    (((parentedNodes 0 κ none (cartesian h)).filter fun q =>
      @decide (FarChildAt (cappedStep μ B) (bandPad u) (bandTolerance u) j (Real.log u/2) q) (Classical.propDecidable _)).map
        (parentWeight (cappedStep μ B) (bandPad u))).sum ≤
      C*weightedCount h cap*u^(-(1-nu)/2) := by
  let C := 8*Real.exp (1-nu)/(1-nu)
  have hden : 0 < 1-nu := by linarith only [nu_lt_one]
  have hC : 0 < C := by dsimp only [C]; positivity
  have ht := tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/10)
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_band_far_child_mass,Real.tendsto_log_atTop.eventually_gt_atTop (2:ℝ),
    eventually_gt_atTop (0:ℝ),ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/4))]
    with u H hlog hu hTolerance
  intro κ B cap μ j h hB hBcap hU hμ hμB hy
  have hδ : 0 ≤ bandTolerance u := (Real.rpow_pos_of_pos hu _).le
  have hδmax : bandTolerance u ≤ 1/4 := by simpa only [bandTolerance,neg_div] using hTolerance.le
  have hwidth : 1 < Real.log u/2 := by linarith only [hlog]
  have HH := H κ B cap μ (bandTolerance u) j (Real.log u/2) h hB hBcap hU hμ hμB hδ hδmax hwidth hy
  have hExp : Real.exp ((nu-1)*(Real.log u/2-1)) = Real.exp (1-nu)*u^(-(1-nu)/2) := by
    rw [Real.rpow_def_of_pos hu,← Real.exp_add]
    congr 1
    ring
  rw [hExp] at HH
  dsimp only [C]
  linear_combination HH

end
end StrongSilver
