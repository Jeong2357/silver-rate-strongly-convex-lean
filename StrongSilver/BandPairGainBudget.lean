-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandPairGainEnvelope

namespace StrongSilver
open ScheduleTree BinaryForest Real Filter Set MeasureTheory
noncomputable section
set_option maxHeartbeats 6500000

theorem eventually_band_group_tolerance : ∀ᶠ u : ℝ in atTop,
    bandTolerance u*(2:ℝ)^fourPhaseDepth u ≤ 1 := by
  filter_upwards [eventually_fourPhaseGroupCount_le_power (by norm_num : (0:ℝ) < 1/10),
    eventually_gt_atTop (0:ℝ)] with u hCount hu
  have hδ : 0 ≤ bandTolerance u := (Real.rpow_pos_of_pos hu _).le
  have hh := mul_le_mul_of_nonneg_left hCount hδ
  have he : bandTolerance u*u^((1:ℝ)/10) = 1 := by
    unfold bandTolerance
    rw [← Real.rpow_add hu]
    norm_num
  rwa [he] at hh

/-- The complete source envelope for the available-pair gains has
an absolute O(W) integral on every subinterval of the outer band. -/
theorem eventually_band_pair_gain_envelope_budget {C : ℝ} (hC : 0 < C) : ∃ K > 0, ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ critical a b : ℝ, ∀ h : List ℝ,
    BandSourceData κ B cap μ critical u h → a ≤ b → outerBandLow u ≤ a → b ≤ outerBandHigh u →
    (∫ y in a..b, bandPairGainEnvelope C κ B cap μ u h y) ≤ K*weightedCount h cap := by
  obtain ⟨Ce,hCe,HE⟩ := eventually_band_endpoint_gain_budget
  obtain ⟨Cd,hCd,HD⟩ := eventually_band_exterior_envelope_budget
  let Cp := bandExcessConstant/(splitCoefficient*nu)
  have hCp : 0 < Cp := div_pos bandExcessConstant_positive (mul_pos split_coefficient_positive nu_positive)
  let K := 4*Cp+2*(19216+8*C)+6*C*Ce+8*Cd
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K,hK,?_⟩
  filter_upwards [eventually_band_positive_log_subinterval,HE,HD,eventually_band_group_tolerance,
    eventually_outerBand_length,eventually_gt_atTop (0:ℝ)] with u hPositive hEndpoint hDraw hCount hLength hu
  intro κ B cap μ critical a b h S hab ha hb
  let L := fun y => max (Real.exp (nu*y)*bandPositiveLog κ B μ u y h) 0
  let E := bandEndpointGainEnvelope κ B μ u h
  let Df := linkedFollowingObservable (cappedStep μ B) (bandPad u) κ nu (bandGoodDrawdownCharge B μ u) h
  let c := (19216+8*C)*weightedCount h cap/u
  have hW := weightedCount_nonneg h cap
  have hδ : 0 ≤ bandTolerance u := (Real.rpow_pos_of_pos hu _).le
  have hLint : IntervalIntegrable L volume a b := intervalIntegrable_positive_part (bandPositiveLog_weighted_integrable κ B μ u a b h)
  have hEint : IntervalIntegrable E volume a b := bandEndpointGainEnvelope_integrable h S.threshold_gt_one S.mu_positive S.curvature_half
  have hDint : IntervalIntegrable Df volume a b := linkedFollowingObservable_integrable (cappedStep μ B)
    (cappedStep_monotone S.mu_positive (by linarith only [S.curvature_half])) (bandPad u) κ nu a b (bandGoodDrawdownCharge B μ u) h
  have hLbound := hPositive κ B cap μ critical a b h S hab ha hb
  have hEbound := hEndpoint κ B cap μ critical a b h S hab
  have hDbound := hDraw κ B cap μ critical a b h S hab
  have hCoefE := mul_le_mul_of_nonneg_left hEbound (show 0 ≤ 6*C*bandTolerance u by positivity)
  have hCountE := mul_le_mul_of_nonneg_left hCount (show 0 ≤ 6*C*Ce*weightedCount h cap by positivity)
  have hEfinal : (6*C*bandTolerance u)*(∫ y in a..b, E y) ≤ 6*C*Ce*weightedCount h cap := by
    linear_combination hCoefE+hCountE
  have hLen : b-a ≤ 2*u := by linarith only [ha,hb,hLength]
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hLenScale := mul_le_mul_of_nonneg_right hLen hc
  have hConst : (∫ _y in a..b, c) ≤ 2*(19216+8*C)*weightedCount h cap := by
    rw [intervalIntegral.integral_const,smul_eq_mul]
    have he : (2*u)*c = 2*(19216+8*C)*weightedCount h cap := by dsimp only [c]; field_simp [hu.ne'] <;> ring
    exact hLenScale.trans_eq he
  have hEq : bandPairGainEnvelope C κ B cap μ u h = fun y => 4*L y+c+(6*C*bandTolerance u)*E y+8*Df y := rfl
  rw [hEq,intervalIntegral.integral_add (((hLint.const_mul 4).add intervalIntegrable_const).add (hEint.const_mul _)) (hDint.const_mul 8),
    intervalIntegral.integral_add ((hLint.const_mul 4).add intervalIntegrable_const) (hEint.const_mul _),
    intervalIntegral.integral_add (hLint.const_mul 4) intervalIntegrable_const,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
  dsimp only [K,Cp,L,Df] at hLbound hDbound ⊢
  linear_combination 4*hLbound+hConst+hEfinal+8*hDbound

/-- The local gain bound used in (4.26), packaged with a measurable
source envelope that dominates every actual reservation pointwise. -/
theorem eventually_band_available_gain : ∃ C > 0, ∃ K > 0, ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ critical a b : ℝ, ∀ h : List ℝ,
    BandSourceData κ B cap μ critical u h → a ≤ b → outerBandLow u ≤ a → b ≤ outerBandHigh u →
    IntervalIntegrable (bandPairGainEnvelope C κ B cap μ u h) volume a b ∧
    (∫ y in a..b, bandPairGainEnvelope C κ B cap μ u h y) ≤ K*weightedCount h cap ∧
    ∀ y ∈ Icc a b, ∀ s : BandPairReservation κ B cap μ u y h,
      Real.exp (nu*y)*((bandPostReservedPairs κ B μ u (Real.log u/200) (fourPhaseDepth u+1) h s.assembly.reserved y).map
        fun p => max (silverDepthGain (cappedStep μ B) (fourPhaseDepth u) p.1.node.source) 0).sum ≤
      bandPairGainEnvelope C κ B cap μ u h y := by
  obtain ⟨C,hC,HG⟩ := eventually_band_pair_gain_envelope
  obtain ⟨K,hK,HB⟩ := eventually_band_pair_gain_envelope_budget hC
  refine ⟨C,hC,K,hK,?_⟩
  filter_upwards [HG,HB] with u hGain hBudget
  intro κ B cap μ critical a b h S hab ha hb
  refine ⟨bandPairGainEnvelope_integrable h S.threshold_gt_one S.mu_positive S.curvature_half,
    hBudget κ B cap μ critical a b h S hab ha hb,?_⟩
  intro y hy s
  exact hGain κ B cap μ critical y h S ⟨ha.trans hy.1,hy.2.trans hb⟩ s

end
end StrongSilver
