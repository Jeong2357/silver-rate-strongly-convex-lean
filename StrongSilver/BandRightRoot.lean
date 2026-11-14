-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandSmallLocalParameters
import StrongSilver.BandLocalLowerScale
import StrongSilver.BandRightGapMass

namespace StrongSilver
open ScheduleTree BinaryForest Scalar.SignedIntervals Real Filter Set
noncomputable section
set_option maxHeartbeats 6800000

theorem internal_node_pivot_mem_word {q : ScheduleNode} (hq : internalNode q = true) : q.pivot ∈ q.source.word := by
  cases hs : q.source with
  | leaf word => simp [internalNode,hs] at hq
  | split l b r => simp [ScheduleNode.pivot,hs,word]

/-- A fixed positive multiple of A eventually dominates A^(1-eta). -/
theorem eventually_subpower_below_scaled_linear {c η : ℝ} (hc : 0 < c) (hη : 0 < η) :
    ∀ᶠ A : ℝ in atTop, A^(1-η) ≤ c*A := by
  filter_upwards [eventually_gt_atTop (0:ℝ),eventually_const_mul_log_pow_le_power 0 (1/c) hη] with A hA hPower
  simp only [pow_zero,mul_one] at hPower
  have hScale := mul_le_mul_of_nonneg_left hPower (mul_nonneg hc.le (Real.rpow_pos_of_pos hA (1-η)).le)
  have hLeft : (c*A^(1-η))*(1/c) = A^(1-η) := by field_simp [hc.ne']
  have hRight : (c*A^(1-η))*A^η = c*A := by
    rw [mul_assoc,← Real.rpow_add hA]
    simp only [sub_add_cancel,Real.rpow_one]
  rwa [hLeft,hRight] at hScale

/-- An actual positive root in the right candidate gap satisfies all
root, signed-mass, lower-scale and curvature conditions of the suffix
construction, with its original finite word index. -/
theorem eventually_band_right_root : ∀ᶠ u : ℝ in atTop,
    ∀ κ B μ y : ℝ, ∀ h : List ℝ, ∀ r : LinkedGap,
    0 < κ → 1 < B → B ≤ κ/128 → u ≤ firstAverageLogScale B → 0 < μ → μ*B ≤ 1/2 →
    y ∈ Icc (outerBandLow u) (outerBandHigh u) →
    r ∈ linkedFrontier (cappedStep μ B) (bandPad u+Real.exp y) 0 κ none none (cartesian h) →
    BandRootCandidate B μ u (Real.log u/200) r y →
    let A := bandCutoff μ u y
    ∃ i : Fin r.node.source.word.length,
      r.node.source.word.get i = r.node.pivot ∧ A^((499:ℝ)/500) ≤ r.node.source.word.get i ∧
      negativeMass r.node.source.word ≤ r.node.source.word.get i/16 ∧
      64*bandLocalLowerScale u A ≤ r.node.source.word.get i ∧
      μ*transformedGapMaximum μ r.node.source.word ≤ 1/1000 := by
  obtain ⟨A₀,hRootPower⟩ := eventually_atTop.mp
    (eventually_subpower_below_scaled_linear bandRootScaleConstant_positive (by norm_num : (0:ℝ) < 1/500))
  filter_upwards [eventually_band_candidate_scale,eventually_band_candidate_upper_scales,eventually_band_negative_scale_small,
    eventually_band_curvature_mass_small (by norm_num : (0:ℝ) < 1/1000),eventually_outer_band_log_window,
    eventually_band_cutoff_ge A₀] with u hScale hUpper hNegative hCurvature hWindow hMinimum
  intro κ B μ y h r hκ hB hBκ hU hμ hμB hy hr hCandidate
  let A := bandCutoff μ u y
  have W := hWindow B μ y hB hU hμ hμB hy
  have hA : 0 < A := W.2.2.1
  have hSc := hScale κ B μ y h r hκ hB hBκ hU hμ hμB hy hr hCandidate.1
  obtain ⟨p,hp,hp0,hpB,hPhi,hpU,hNeg⟩ := hUpper κ B μ y h r hκ.le hB hU hμ hμB hy hr hCandidate
  have hNegSmall := hNeg.trans (hNegative A r.node.pivot hA.le hSc.1)
  have hLower := (band_local_lower_scale_bounds u A (bandRootScaleConstant*A) r.node.pivot hA le_rfl hSc.1).2.2
  have hPower : A^((499:ℝ)/500) ≤ r.node.pivot := by
    have hh := hRootPower A (hMinimum B μ y hB hU hμ hμB hy)
    norm_num at hh
    exact hh.trans hSc.1
  have hPrefix := prefixMass_capped (μ:=μ) r.node.source hSc.2.2.2.2
  have hTransform := capped_gapPrefix_eq hμ (show μ*B < 1 by linarith only [hμB]) r.node.source.word hSc.2.2.2.2
  have hMassEq : r.node.source.prefixMass (logarithmicStep μ) = transformedGapMaximum μ r.node.source.word+1 := by
    rw [← hPrefix]
    change gapPrefix (cappedStep μ B) r.node.source.word+1 = _
    rw [hTransform]
  have hMassUpper : transformedGapMaximum μ r.node.source.word ≤ 36*A := by
    have hh := hSc.2.2.2.1
    rw [hMassEq] at hh
    linarith only [hh]
  have hMuMass := hCurvature B μ y (transformedGapMaximum μ r.node.source.word) hB hU hμ hμB hy hMassUpper
  have hMem := internal_node_pivot_mem_word (bandGoodBool_internal hCandidate.1.1)
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hMem
  refine ⟨i,hi,?_,?_,?_,hMuMass⟩
  · simpa only [hi] using hPower
  · simpa only [hi] using hNegSmall
  · simpa only [hi] using hLower

end
end StrongSilver
