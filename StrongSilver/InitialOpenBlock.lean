-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.InitialTraceLogPrices
import StrongSilver.NoLeftTerminal

namespace StrongSilver
open Real
noncomputable section
set_option maxHeartbeats 2600000

theorem initialBlockConstant_dominates_radius : initialConeRadiusConstant ≤ initialBlockConstant := by
  have hh := mul_nonneg initialEntryConstant_positive.le initialConeRadiusConstant_positive.le
  unfold initialBlockConstant
  nlinarith only [hh]

/-- At the first step, the initial cone block does not require a positive
source. Its actual suffix is retained with the same polynomial entry price. -/
theorem initial_open_block_distance_lower {κ B μ c r : ℝ}
    (hκ : 1 ≤ κ) (hB : 0 < B) (hBκ : B ≤ κ) (hμ : 1/κ ≤ μ) (hμ1 : μ ≤ 1)
    (hc : 2 ≤ c) (hcB : B ≤ c) (hcκ : c ≤ κ) (hqc : 1/32 ≤ 1-μ*c)
    (I s : List ℝ) (hcritical : ∀ a ∈ I, 1-μ*a ≠ 0)
    (S : PositiveTrace μ s (initialGateConstant/(κ/B)^2) (initialPointRelativeConstant*(κ/B))
      (initialSlopeRelativeConstant*(κ/B)/κ) r) :
    ENNReal.ofReal (r/(initialBlockFactor κ B μ I)^2) ≤ D κ ((I++[c])++s) := by
  let K := κ/B
  have hκ0 := zero_lt_one.trans_le hκ
  have hμ0 : 0 < μ := (one_div_pos.mpr hκ0).trans_le hμ
  have hK : 1 ≤ K := (one_le_div hB).mpr hBκ
  have hK0 := zero_lt_one.trans_le hK
  have hV := norm_pos_iff.mpr S.nonzero
  have hK2 : 1 ≤ K^2 := by nlinarith only [hK]
  have hη : 0 < initialGateConstant/K^2 := div_pos initialGateConstant_positive (sq_pos_of_pos hK0)
  have hη1 : initialGateConstant/K^2 ≤ 1 := (div_le_one (sq_pos_of_pos hK0)).mpr (initialGateConstant_le_one.trans hK2)
  have hM : 1 ≤ initialPointRelativeConstant*K := by
    have hh := mul_le_mul initialPointRelativeConstant_ge_one hK (by norm_num : (0 : ℝ) ≤ 1) initialPointRelativeConstant_positive.le
    simpa only [one_mul] using hh
  have hH : 0 ≤ initialSlopeRelativeConstant*K*‖S.path.x 0‖/κ := by
    have hh := initialSlopeRelativeConstant_positive
    positivity
  have hminus : S.path.family.Gate (S.path.x 0) (-(initialGateConstant/K^2)) :=
    S.path.family.gate_below S.positive.2 S.gate (by linarith only [hη])
  have hqueries (j) : |inner ℝ (unitDirection (S.path.x 0)) (S.path.family.z j)| ≤ initialPointRelativeConstant*K*‖S.path.x 0‖ ∧
      |inner ℝ (unitDirection (S.path.x 0)) (S.path.family.g j)| ≤ initialSlopeRelativeConstant*K*‖S.path.x 0‖/κ := by
    refine ⟨(S.projections j).1,(S.projections j).2.trans_eq ?_⟩
    ring
  obtain ⟨C,n,Q,hQ,hN,hend,hsteps,hz,hg⟩ := two_cone_attachment hμ0 hc (by linarith only [hqc]) hV hM hH hη hη1
    I hcritical S.path (unitDirection (S.path.x 0)) (unitDirection_inner S.nonzero) (norm_smul_unitDirection S.nonzero).symm
    (fun j => (hqueries j).1) (fun j => (hqueries j).2) S.gate hminus
  have hκKc : κ ≤ K*c := by
    have hh := mul_le_mul_of_nonneg_left hcB hK0.le
    have he : K*B = κ := by dsimp only [K]; field_simp
    rwa [he] at hh
  have htrace := C.initial_trace_radius hμ0.le hc hcκ hκ0 hK hV hκKc hqc I
  have hKpow : K^4 ≤ K^6 := by
    have hh := mul_le_mul_of_nonneg_left hK2 (show 0 ≤ K^4 by positivity)
    nlinarith only [hh]
  have hcoef : initialConeRadiusConstant*K^4 ≤ initialBlockConstant*K^6 :=
    mul_le_mul initialBlockConstant_dominates_radius hKpow (by positivity) initialBlockConstant_positive.le
  have hNfactor : ‖Q.x 0‖ ≤ initialBlockFactor κ B μ I*‖S.path.x 0‖ := by
    have hs : 0 ≤ 1+smallPositiveSum μ I/κ := by have hh := div_nonneg (smallPositiveSum_nonneg μ I) hκ0.le; linarith only [hh]
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef hV.le)
      (Real.exp_pos (inverseCharge μ I)).le) hs
    apply (hN.trans htrace).trans (hh.trans_eq ?_)
    unfold initialBlockFactor
    dsimp only [K]
    ring
  have hEndNorm : ‖Q.x (Fin.last n)‖ = ‖S.path.x (Fin.last S.length)‖ := by
    rw [hend]
    exact retainedIsometry.norm_map _
  have hactual := ratio_lower_of_source_scale hV (norm_pos_iff.mpr hQ) (initialBlockFactor_positive hκ0 hB μ I)
    (norm_nonneg (S.path.x (Fin.last S.length))) hEndNorm.symm.le hNfactor
  have hratio := (div_le_div_of_nonneg_right S.ratio (sq_nonneg (initialBlockFactor κ B μ I))).trans hactual
  have hh := (ENNReal.ofReal_le_ofReal hratio).trans (Q.finite_distance_lower hκ hμ hμ1 hQ)
  have hstepseq := hsteps.trans (congrArg (fun l : List ℝ => (I++[c])++l) S.steps_eq)
  simpa only [hstepseq] using hh

end
end StrongSilver
