-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandFullKernelEnvelope
import StrongSilver.BandKernelErrorRate

namespace StrongSilver
open ScheduleTree BinaryForest Real Filter Set MeasureTheory
noncomputable section
set_option maxHeartbeats 11000000

theorem boundary_depth_factor {δ : ℝ} (hδ : 0 ≤ δ) {d k : ℕ} (hk : k ≤ d+2) :
    (2:ℝ)^k*(k:ℝ)*δ ≤ 4*(2:ℝ)^d*((d:ℝ)+2)*δ := by
  have hp : (2:ℝ)^k ≤ (2:ℝ)^(d+2) := by exact_mod_cast Nat.pow_le_pow_right (by decide : 1 ≤ 2) hk
  rw [pow_add] at hp
  norm_num at hp
  have hPow : (2:ℝ)^k ≤ 4*(2:ℝ)^d := by linear_combination hp
  have hkr : (k:ℝ) ≤ (d:ℝ)+2 := by exact_mod_cast hk
  exact mul_le_mul_of_nonneg_right (mul_le_mul hPow hkr (Nat.cast_nonneg _) (by positivity)) hδ

/-- Before normalization, all available-gap kernel terms have an
O(W*(1+2^d*((d+2)*delta+u*exp(-u/100)))) integral. -/
theorem eventually_band_available_kernel_budget {C : ℝ} (hC : 0 < C) : ∃ K > 0, ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ critical a b : ℝ, ∀ h : List ℝ,
    BandSourceData κ B cap μ critical u h → a ≤ b → innerBandLow u ≤ a → b ≤ innerBandHigh u →
    (∫ y in a..b, bandAvailableKernelEnvelope C κ B cap μ u h y) ≤
      K*weightedCount h cap*(1+(2:ℝ)^fourPhaseDepth u*
        (((fourPhaseDepth u:ℝ)+2)*bandTolerance u+u*Real.exp (-u/100))) := by
  obtain ⟨Cp,hCp,HP⟩ := eventually_band_pair_gain_envelope_budget hC
  obtain ⟨Ct,hCt,HT⟩ := eventually_band_through_gain_budget
  obtain ⟨Cb,hCb,HB⟩ := eventually_band_boundary_envelope_budget
  let K0 := splitCoefficient*Cp
  let K1 := 2*splitCoefficient*Ct+12*Cb
  let K2 := 768*splitCoefficient
  let K := K0+K1+K2
  have hCf := split_coefficient_positive
  have hK0 : 0 < K0 := by dsimp only [K0]; positivity
  have hK1 : 0 < K1 := by dsimp only [K1]; positivity
  have hK2 : 0 < K2 := by dsimp only [K2]; positivity
  refine ⟨K,by dsimp only [K]; positivity,?_⟩
  filter_upwards [HP,HT,HB,eventually_inner_band_geometry,eventually_outerBand_length,eventually_ge_atTop (1:ℝ)]
    with u hPair hThrough hBoundary hGeometry hLength hu
  intro κ B cap μ critical a b h S hab ha hb
  let d := fourPhaseDepth u
  let N := (2:ℝ)^d
  let W := weightedCount h cap
  let X := ((d:ℝ)+2)*bandTolerance u
  let Z := u*Real.exp (-u/100)
  have hu0 := zero_lt_one.trans_le hu
  have hδ : 0 ≤ bandTolerance u := (Real.rpow_pos_of_pos hu0 _).le
  have hW : 0 ≤ W := weightedCount_nonneg h cap
  have hN : 0 ≤ N := by dsimp only [N]; positivity
  have hX : 0 ≤ X := by dsimp only [X]; positivity
  have hZ : 0 ≤ Z := by dsimp only [Z]; positivity
  have haOuter : outerBandLow u ≤ a := hGeometry.2.2.2.1.le.trans ha
  have hLog : 0 ≤ Real.log u/200 := div_nonneg (Real.log_nonneg hu) (by norm_num)
  have hbOuter : b ≤ outerBandHigh u := by
    have hh := hGeometry.2.2.2.2.1
    linarith only [hb,hh,hLog,visibilitySpacing_positive]
  have hLen : b-a ≤ 2*u := by linarith only [haOuter,hbOuter,hLength]
  have hPint := bandPairGainEnvelope_integrable (C:=C) (κ:=κ) (cap:=cap) (u:=u) (a:=a) (b:=b) h S.threshold_gt_one S.mu_positive S.curvature_half
  have hTint := linkedGoodThroughObservable_integrable (κ:=κ) (u:=u) (a:=a) (b:=b) (bandGoodGainCharge B μ u) h S.threshold_gt_one S.mu_positive S.curvature_half (d+2)
  have hBint (k : ℕ) := bandBoundaryEnvelope_integrable κ B μ u a b k h
  have hP := mul_le_mul_of_nonneg_left (hPair κ B cap μ critical a b h S hab haOuter hbOuter) hCf.le
  have hT := mul_le_mul_of_nonneg_left (hThrough κ B cap μ critical a b h S hab)
    (show 0 ≤ 2*splitCoefficient*bandTolerance u by positivity)
  have hδX : bandTolerance u ≤ X := by
    dsimp only [X]
    have hn : (1:ℝ) ≤ (d:ℝ)+2 := by have hd0 := Nat.cast_nonneg (α:=ℝ) d; linarith only [hd0]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hn hδ
  have hTX := mul_le_mul_of_nonneg_left hδX (show 0 ≤ 2*splitCoefficient*Ct*N*W by positivity)
  have hTfinal : (2*splitCoefficient*bandTolerance u)*(∫ y in a..b,
      linkedGoodThroughObservable κ B μ u (bandGoodGainCharge B μ u) h (d+2) y) ≤ 2*splitCoefficient*Ct*N*X*W := by
    dsimp only [d,N,W] at hTX ⊢
    linear_combination hT+hTX
  have hB (k : ℕ) (hk : k ≤ d+2) : (∫ y in a..b, bandBoundaryEnvelope κ B μ u k h y) ≤ 4*Cb*N*X*W := by
    have hh := hBoundary κ B cap μ critical a b h k S hab hk
    have hScale := mul_le_mul_of_nonneg_left (boundary_depth_factor hδ hk) (show 0 ≤ Cb*W by positivity)
    dsimp only [N,X,W] at hScale ⊢
    linear_combination hh+hScale
  have hB0 := hB d (by omega)
  have hB1 := hB (d+1) (by omega)
  have hB2 := hB (d+2) (by omega)
  let c := 384*splitCoefficient*Real.exp (-u/100)*N*W
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hConstScale := mul_le_mul_of_nonneg_right hLen hc
  have hConst : (∫ _y in a..b, c) ≤ K2*N*Z*W := by
    rw [intervalIntegral.integral_const,smul_eq_mul]
    dsimp only [K2,Z,c] at hConstScale ⊢
    linear_combination hConstScale
  have hEq : bandAvailableKernelEnvelope C κ B cap μ u h = fun y =>
      splitCoefficient*bandPairGainEnvelope C κ B cap μ u h y+
      (2*splitCoefficient*bandTolerance u)*linkedGoodThroughObservable κ B μ u (bandGoodGainCharge B μ u) h (d+2) y+c+
      bandBoundaryEnvelope κ B μ u d h y+bandBoundaryEnvelope κ B μ u (d+1) h y+bandBoundaryEnvelope κ B μ u (d+2) h y := rfl
  rw [hEq,intervalIntegral.integral_add
    (((((hPint.const_mul _).add (hTint.const_mul _)).add intervalIntegrable_const).add (hBint d)).add (hBint (d+1))) (hBint (d+2)),
    intervalIntegral.integral_add ((((hPint.const_mul _).add (hTint.const_mul _)).add intervalIntegrable_const).add (hBint d)) (hBint (d+1)),
    intervalIntegral.integral_add (((hPint.const_mul _).add (hTint.const_mul _)).add intervalIntegrable_const) (hBint d),
    intervalIntegral.integral_add ((hPint.const_mul _).add (hTint.const_mul _)) intervalIntegrable_const,
    intervalIntegral.integral_add (hPint.const_mul _) (hTint.const_mul _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
  have hRaw : splitCoefficient*(∫ y in a..b, bandPairGainEnvelope C κ B cap μ u h y)+
      (2*splitCoefficient*bandTolerance u)*(∫ y in a..b, linkedGoodThroughObservable κ B μ u (bandGoodGainCharge B μ u) h (d+2) y)+
      (∫ _y in a..b,c)+(∫ y in a..b,bandBoundaryEnvelope κ B μ u d h y)+
      (∫ y in a..b,bandBoundaryEnvelope κ B μ u (d+1) h y)+(∫ y in a..b,bandBoundaryEnvelope κ B μ u (d+2) h y) ≤
      K0*W+K1*N*X*W+K2*N*Z*W := by
    dsimp only [K0,K1,W] at hP ⊢
    linear_combination hP+hTfinal+hConst+hB0+hB1+hB2
  have hK0le : K0 ≤ K := by dsimp only [K]; linarith only [hK1,hK2]
  have hK1le : K1 ≤ K := by dsimp only [K]; linarith only [hK0,hK2]
  have hK2le : K2 ≤ K := by dsimp only [K]; linarith only [hK0,hK1]
  apply hRaw.trans
  calc
    _ ≤ K*W+K*N*X*W+K*N*Z*W := by gcongr
    _ = _ := by dsimp only [W,N,X,Z,d]; ring

end
end StrongSilver
