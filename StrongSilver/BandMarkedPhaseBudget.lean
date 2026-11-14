-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.WorkingMarkedRankDecay
import StrongSilver.BandPointwiseBounds

namespace StrongSilver
open Real Filter Set
noncomputable section
set_option maxHeartbeats 6400000

/-- Uniform weighted ordinary-phase failure count. This implies an
O(W) integrated reservation budget on a band of length O(u), which is
sufficient for the pair-availability estimate. -/
theorem eventually_band_marked_phase_budget : ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ : ℝ, ∀ h : List ℝ,
    1 < κ → 1 < B → B ≤ cap → cap ≤ κ → u ≤ firstAverageLogScale B →
    0 < μ → μ*B ≤ 1/2 → D κ h ≤ 1 →
    ∀ y ∈ Icc (outerBandLow u) (outerBandHigh u),
    let A := bandCutoff μ u y
    Real.exp (nu*y)*(badPhaseCount (ordinaryPhaseGood A μ (A^(1+bandUpsilon firstAverageEta)) (bandPad u))
      (bandFullCut μ u y h).phases:ℝ) ≤ 4*weightedCount h cap/u := by
  have hη := firstAverageEta_bounds.1
  have hη1 : firstAverageEta < 1 := firstAverageEta_bounds.2.trans (by norm_num)
  obtain ⟨hσ,hσmax,hτ,hτmax,hσυ,hτυ,hυmax,hυq⟩ := band_exponent_bounds hη firstAverageEta_small
  obtain ⟨A₀,hSource⟩ := eventually_atTop.mp
    (eventually_working_marked_rank_decay hσ hσmax hτ hτmax hσυ hτυ hυmax hυq)
  filter_upwards [eventually_outer_band_log_window,eventually_band_cutoff_ge A₀,eventually_band_cutoff_ge 2,
    eventually_gt_atTop (0:ℝ)] with u hWindow hMinimum hTwo hu
  intro κ B cap μ h hκ hB hBcap hcapκ hU hμ hμB hD y hy
  let A := bandCutoff μ u y
  let C := bandFullCut μ u y h
  have W := hWindow B μ y hB hU hμ hμB hy
  have hA0 : 0 < A := W.2.2.1
  have hA2 : 2 ≤ A := hTwo B μ y hB hU hμ hμB hy
  have hA1 : 1 < A := lt_of_lt_of_le (by norm_num) hA2
  have hHalf : u/2 ≤ Real.log A := W.2.2.2.2.2.2.2.2.2.1
  have hLog : 0 < Real.log A := (by linarith only [hu] : 0 < u/2).trans_le hHalf
  have hAupper : A ≤ B^(1-firstAverageEta) := W.2.2.2.2.2.2.2.2.1
  have hGap := band_cutoff_power_gap hη hη1 hA0 (zero_lt_one.trans hB) hAupper
  have hWord : C.word = h := cutSchedule_word _ _
  have hPiv : ∀ p ∈ C.phases, A^((499:ℝ)/500) ≤ p.pivot := by
    intro p hp
    have hl : A^((499:ℝ)/500) ≤ A := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hA1.le (by norm_num : (499:ℝ)/500 ≤ 1)
    exact hl.trans (fullCut_pivot hp).le
  have hSmall : ∀ b ∈ C.unselected, 0 < b → b ≤ A := fun b hb _ => fullCut_unselected hb
  have hMarked := hSource A (hMinimum B μ y hB hU hμ hμB hy) κ B cap μ (bandPad u) C
    hκ hGap hBcap hcapκ hμ hμB W.2.2.2.2.2.1 W.2.2.2.2.2.2.1 hPiv hSmall (by simpa only [hWord] using hD)
  rw [hWord] at hMarked
  have hP : 0 < bandPad u := Real.exp_pos _
  have hSize := logarithmicCutoff_size hμ hP.le W.2.1
  have hHeight : Real.exp y ≤ 2*A := by dsimp only [A,bandCutoff]; linarith only [hSize.1,hP]
  have hNorm := height_power_normalization hA0 hHeight
  have hScaled := mul_le_mul_of_nonneg_left hMarked (Real.exp_pos (nu*y)).le
  have hW := weightedCount_nonneg h cap
  have hCancel := mul_le_mul_of_nonneg_left hNorm (div_nonneg hW hLog.le)
  have hInv : 1/Real.log A ≤ 2/u := by
    have hh := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1) (by positivity : 0 < u/2) hHalf
    convert hh using 1 <;> first | rfl | ring
  have hInverse := mul_le_mul_of_nonneg_left hInv (show 0 ≤ 2*weightedCount h cap by positivity)
  change Real.exp (nu*y)*(badPhaseCount (ordinaryPhaseGood A μ (A^(1+bandUpsilon firstAverageEta)) (bandPad u)) C.phases:ℝ) ≤ _
  linear_combination hScaled+hCancel+hInverse

end
end StrongSilver
