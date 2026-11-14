-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.HeightStripRank
import StrongSilver.BandBinGeometry
import StrongSilver.BandFrontierMassBudget

namespace StrongSilver
open ScheduleTree Real Filter Set
noncomputable section
set_option maxHeartbeats 4600000

def bandLowerStripNodes (κ B μ u : ℝ) (h : List ℝ) : List ParentedScheduleNode :=
  (bandProtectedNodes κ B μ u h).filter fun q => decide
    (parentedHeight (cappedStep μ B) (bandPad u) q ≤ outerBandLow u+bandBinWidth u)

/-- The lower boundary strip in (4.23) costs at most 2 W u^(2/5).
This bound counts original occurrences and does not assume a mass or
rank estimate as an additional premise. -/
theorem eventually_band_lower_strip_weight : ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ : ℝ, ∀ h : List ℝ,
    1 < B → B ≤ cap → u ≤ firstAverageLogScale B → 0 < μ → μ*B ≤ 1/2 →
    ((bandLowerStripNodes κ B μ u h).map fun q => Real.exp (nu*parentedHeight (cappedStep μ B) (bandPad u) q)).sum ≤
      2*weightedCount h cap*u^((2:ℝ)/5) := by
  filter_upwards [eventually_outer_band_log_window,eventually_ge_atTop (1:ℝ)] with u hWindow hu
  intro κ B cap μ h hB hBcap hU hμ hμB
  have hu0 := zero_lt_one.trans_le hu
  have hOrder := outerBand_order hu0.le
  have W := hWindow B μ (outerBandLow u) hB hU hμ hμB ⟨le_rfl,hOrder⟩
  have hsize := logarithmicCutoff_size hμ (show (0:ℝ) ≤ bandPad u by exact (Real.exp_pos _).le) W.2.1
  have hη := firstAverageEta_bounds.1
  have hBpower : B^(1-firstAverageEta) ≤ B := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hB.le
      (show 1-firstAverageEta ≤ (1:ℝ) by linarith only [hη])
  have hAcut : logarithmicCutoff μ (bandPad u) (outerBandLow u) ≤ cap :=
    (W.2.2.2.2.2.2.2.2.1.trans hBpower).trans hBcap
  have hAcap : Real.exp (outerBandLow u)/2 ≤ cap := by
    have hp := Real.exp_pos ((987:ℝ)/1000*u)
    change 0 < bandPad u at hp
    linarith only [hsize.1,hAcut,hp]
  let f := heightStripWeight (cappedStep μ B) (bandPad u) (outerBandLow u) (bandBinWidth u)
  let qs := bandLowerStripNodes κ B μ u h
  have hMap : (qs.map fun q => Real.exp (nu*parentedHeight (cappedStep μ B) (bandPad u) q)).sum =
      (qs.map fun q => f q.node.pivot).sum := by
    congr 1
    apply List.map_congr_left
    intro q hq
    obtain ⟨hp,hs⟩ := List.mem_filter.mp hq
    have hh := of_decide_eq_true (List.mem_filter.mp hp).2
    have hStrip := of_decide_eq_true hs
    have hSelect : bandPad u < cappedStep μ B q.node.pivot ∧
        outerBandLow u ≤ Real.log (cappedStep μ B q.node.pivot-bandPad u) ∧
        Real.log (cappedStep μ B q.node.pivot-bandPad u) ≤ outerBandLow u+bandBinWidth u :=
      ⟨hh.1,hh.2.2.1.le,hStrip⟩
    dsimp only [f,heightStripWeight]
    rw [if_pos hSelect]
    rfl
  rw [hMap]
  have hsub : qs.Sublist (parentedNodes 0 κ none (cartesian h)) := List.filter_sublist.trans List.filter_sublist
  have hsum := (hsub.map fun q => f q.node.pivot).sum_le_sum (by
    intro x hx
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hx
    exact heightStripWeight_nonnegative _ _ _ _ _)
  have hWord := parentedPivotWeight_le_word f (heightStripWeight_nonnegative _ _ _ _) κ (cartesian h)
  rw [cartesian_word] at hWord
  have hRank := height_strip_word_rank (P := bandPad u) (width := bandBinWidth u) hμ (zero_lt_one.trans hB) hμB (Real.exp_pos _) hAcap h
  have hExp : Real.exp (nu*bandBinWidth u) = u^(nu/2) := by
    rw [bandBinWidth,Real.rpow_def_of_pos hu0]
    congr 1
    ring
  have hRank' : (h.map f).sum ≤ 2*weightedCount h cap*u^(nu/2) := by simpa only [hExp] using hRank
  have hPower := Real.rpow_le_rpow_of_exponent_le hu (show nu/2 ≤ (2:ℝ)/5 by linarith only [nu_lt_four_fifths])
  have hFinal := mul_le_mul_of_nonneg_left hPower (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (weightedCount_nonneg h cap))
  exact (hsum.trans (hWord.trans hRank')).trans hFinal

end
end StrongSilver
