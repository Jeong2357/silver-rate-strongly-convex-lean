-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandCandidateHeight
import StrongSilver.GoodThroughSourceBalance
import StrongSilver.SilverBalancedRootMass
import StrongSilver.CappedSourceBalance
import StrongSilver.HeightStripRank

namespace StrongSilver
open ScheduleTree BinaryForest Real Filter Set
noncomputable section
set_option maxHeartbeats 6800000

def bandRootScaleConstant : ℝ := Real.exp (-3)/4

theorem bandRootScaleConstant_positive : 0 < bandRootScaleConstant := div_pos (Real.exp_pos _) (by norm_num)

/-- The actual root step and actual signed logarithmic prefix mass of
an S(y) gap are comparable to the inverse cutoff A. Every source step
lies below the original transform cap. -/
theorem eventually_band_candidate_scale : ∀ᶠ u : ℝ in atTop,
    ∀ κ B μ y : ℝ, ∀ h : List ℝ, ∀ q : LinkedGap,
    0 < κ → 1 < B → B ≤ κ/128 → u ≤ firstAverageLogScale B → 0 < μ → μ*B ≤ 1/2 →
    y ∈ Icc (outerBandLow u) (outerBandHigh u) →
    q ∈ linkedFrontier (cappedStep μ B) (bandPad u+Real.exp y) 0 κ none none (cartesian h) → GoodLinkedRoot B μ u q →
    let A := bandCutoff μ u y
    bandRootScaleConstant*A ≤ q.node.pivot ∧ q.node.pivot ≤ A ∧
      bandRootScaleConstant*A ≤ q.node.source.prefixMass (logarithmicStep μ) ∧
      q.node.source.prefixMass (logarithmicStep μ) ≤ 36*A ∧ (∀ s ∈ q.node.source.word, s ≤ B) := by
  filter_upwards [eventually_band_candidate_height,eventually_band_good_source_balance,eventually_outer_band_log_window,
    eventually_band_pad_small,eventually_band_forest_spacing] with u hHeight hBalance hWindow hPad hTol
  intro κ B μ y h q hκ hB hBκ hU hμ hμB hy hq hGood
  let φ := cappedStep μ B
  let P := bandPad u
  let A := bandCutoff μ u y
  have hG := (bandGoodBool_iff B μ u q.node).mp hGood.1
  have hMem := linkedFrontier_internal_mem hq (bandGoodBool_internal hGood.1)
  have hCart := indexedTree_source_cartesian (cartesian_valid h) hMem
  have hSilver := hBalance κ B μ h q.node hκ hB hBκ hU hμ hμB hMem hGood.1
  have hε : 4*bandTolerance u ≤ 1/4 := by linarith only [hTol.2.1]
  have hMass := silverBalanced_root_mass hε hSilver
  have W := hWindow B μ y hB hU hμ hμB hy
  have hA : 0 < A := W.2.2.1
  have hP : 0 < P := Real.exp_pos _
  have hPquarter : P ≤ Real.exp y/4 := (hPad.2 y hy.1).1
  have hPexp : P ≤ Real.exp y := by linarith only [hPquarter,Real.exp_pos y]
  have hSize := logarithmicCutoff_size hμ hP.le W.2.1
  have hAupper : A ≤ 2*Real.exp y := by dsimp only [A,bandCutoff]; linarith only [hSize.2.1,hPexp]
  have hAlower : Real.exp y ≤ 2*A := by dsimp only [A,bandCutoff]; linarith only [hSize.1,hP]
  have hη := firstAverageEta_bounds.1
  have hBpower : B^(1-firstAverageEta) ≤ B := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hB.le (show 1-firstAverageEta ≤ (1:ℝ) by linarith only [hη])
  have hAB : A ≤ B := W.2.2.2.2.2.2.2.2.1.trans hBpower
  have hBranch : φ A = P+Real.exp y := W.2.2.2.2.2.2.2.2.2.2
  have hStrict := cappedStep_strictMono (B:=B) hμ (by linarith only [hμB])
  have hZero : φ 0 = 0 := by simp only [φ,cappedStep,if_pos (zero_lt_one.trans hB).le,logarithmicStep_zero]
  have hRootφPos : φ 0 < φ q.node.pivot := by rw [hZero]; exact hP.trans hG.2.1
  have hRootPos : 0 < q.node.pivot := hStrict.lt_iff_lt.mp hRootφPos
  have hRootMem : q.node ∈ indexedFrontier φ (P+Real.exp y) 0 κ (cartesian h) := by
    rw [← linkedFrontier_erase φ (P+Real.exp y) 0 κ none none (cartesian h)]
    exact List.mem_map.mpr ⟨q,hq,rfl⟩
  have hRootUpper := indexedFrontier_root_upper (show φ 0 ≤ P+Real.exp y by rw [hZero]; positivity) hRootMem
  change φ q.node.pivot ≤ P+Real.exp y at hRootUpper
  have hRootA : q.node.pivot ≤ A := hStrict.le_iff_le.mp (hRootUpper.trans_eq hBranch.symm)
  have hWord : ∀ s ∈ q.node.source.word, s ≤ B := fun s hs =>
    (cartesian_word_le_root hCart hs).trans (hRootA.trans hAB)
  have hφUpper : φ q.node.pivot ≤ 2*q.node.pivot := by
    have H := cappedStep_positive_upper_global hμ (zero_lt_one.trans hB) hμB q.node.pivot
    rw [max_eq_left hRootPos.le] at H
    exact (le_max_left _ _).trans H
  have hH := hHeight κ B μ y h q hκ.le hB hμB hq hGood
  have hLogRho : Real.log rho ≤ 2 := (Real.log_le_sub_one_of_pos rho_positive).trans (by linarith only [rho_bounds.2])
  have hHUpper : y-nodePaddedHeight φ P q.node ≤ Real.log rho+11*bandTolerance u := hH.2
  have hHeightLower : y-3 ≤ nodePaddedHeight φ P q.node := by linarith only [hHUpper,hLogRho,hTol.2.1]
  have hTime := Real.exp_le_exp.mpr hHeightLower
  have hTimeEq : Real.exp (nodePaddedHeight φ P q.node) = φ q.node.pivot-P := Real.exp_log (sub_pos.mpr hG.2.1)
  rw [hTimeEq,show y-3 = (-3)+y by ring,Real.exp_add] at hTime
  have hAweighted := mul_le_mul_of_nonneg_left hAupper bandRootScaleConstant_positive.le
  have hRootLower : bandRootScaleConstant*A ≤ q.node.pivot := by
    dsimp only [bandRootScaleConstant] at hAweighted ⊢
    nlinarith only [hAweighted,hTime,hφUpper,hP]
  have hRootGe : q.node.pivot ≤ φ q.node.pivot := cappedStep_ge (B:=B) hμ (by linarith only [hμB]) _
  have hMassLower : bandRootScaleConstant*A ≤ q.node.source.prefixMass φ := hRootLower.trans (hRootGe.trans hMass.1)
  have hMassUpper : q.node.source.prefixMass φ ≤ 36*A := by
    have hm : q.node.source.prefixMass φ ≤ 9*φ q.node.pivot := hMass.2
    linarith only [hm,hRootUpper,hPexp,hAlower]
  have hPrefix := prefixMass_capped (μ:=μ) q.node.source hWord
  refine ⟨hRootLower,hRootA,?_,?_,hWord⟩
  · simpa only [φ,hPrefix] using hMassLower
  · simpa only [φ,hPrefix] using hMassUpper

end
end StrongSilver
