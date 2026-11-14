-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandAvailableKernelBudget
import StrongSilver.BandRefinementIntegral

namespace StrongSilver
open ScheduleTree BinaryForest Real Filter Set MeasureTheory
noncomputable section
set_option maxHeartbeats 10500000

theorem rpow_div_self {u : ℝ} (hu : 0 < u) (r : ℝ) : u^r/u = u^(r-1) := by
  calc
    _ = u^r/u^(1:ℝ) := by rw [Real.rpow_one]
    _ = _ := (Real.rpow_sub hu r 1).symm

/-- The full explicit source envelope, including the excluded forest,
has the unnormalized kernel budget on every inner-band interval. -/
theorem eventually_band_full_kernel_budget {C : ℝ} (hC : 0 < C) : ∃ K > 0, ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ critical a b : ℝ, ∀ h : List ℝ,
    BandSourceData κ B cap μ critical u h → a ≤ b → innerBandLow u ≤ a → b ≤ innerBandHigh u →
    (∫ y in a..b, bandFullKernelEnvelope C κ B cap μ u h y) ≤
      K*weightedCount h cap*(1+(2:ℝ)^fourPhaseDepth u*bandKernelError u) := by
  obtain ⟨Ka,hKa,HA⟩ := eventually_band_available_kernel_budget hC
  obtain ⟨Kv,hKv,HV⟩ := eventually_band_availability_budget
  let Ks := 2*splitCoefficient*bandIntegralConstant
  let Ke := 153600*splitCoefficient*Kv
  let K := Ka+Ks+Ke
  have hCf := split_coefficient_positive
  have hKs : 0 < Ks := by dsimp only [Ks]; have hI := bandIntegralConstant_positive; positivity
  have hKe : 0 < Ke := by dsimp only [Ke]; positivity
  refine ⟨K,by dsimp only [K]; positivity,?_⟩
  filter_upwards [HA,HV,eventually_band_refinement_subinterval,eventually_inner_band_geometry,eventually_ge_atTop (1:ℝ)]
    with u hAvailable hAvailability hSavings hGeometry hu
  intro κ B cap μ critical a b h S hab ha hb
  let N := (2:ℝ)^fourPhaseDepth u
  let W := weightedCount h cap
  let Ea := ((fourPhaseDepth u:ℝ)+2)*bandTolerance u+u*Real.exp (-u/100)
  let Eb := u^(-(1:ℝ)/10)*N+u^(-nu/200)
  let M := (153600*splitCoefficient)*N/u
  have hu0 := zero_lt_one.trans_le hu
  have hW : 0 ≤ W := weightedCount_nonneg h cap
  have hN : 0 ≤ N := by dsimp only [N]; positivity
  have hδ : 0 ≤ bandTolerance u := (Real.rpow_pos_of_pos hu0 _).le
  have hEa : 0 ≤ Ea := by dsimp only [Ea]; positivity
  have hEb : 0 ≤ Eb := by dsimp only [Eb]; positivity
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have haOuter : outerBandLow u < a := hGeometry.2.2.2.1.trans_le ha
  have hbMargin : b+Real.log u/200+3*visibilitySpacing ≤ outerBandHigh u := by
    have hh := hGeometry.2.2.2.2.1
    linarith only [hb,hh]
  have hbOuter : b ≤ outerBandHigh u := by
    have hLog : 0 ≤ Real.log u/200 := div_nonneg (Real.log_nonneg hu) (by norm_num)
    linarith only [hbMargin,hLog,visibilitySpacing_positive]
  have hA := hAvailable κ B cap μ critical a b h S hab ha hb
  have hS := mul_le_mul_of_nonneg_left (hSavings κ B cap μ critical a b h S hab haOuter.le hbOuter)
    (show 0 ≤ 2*splitCoefficient by positivity)
  have hV := hAvailability κ B cap μ critical a b h S.kappa_gt_one S.threshold_gt_one S.threshold_le_cap S.cap_le_kappa
    S.threshold_small S.scale_upper S.curvature_lower S.curvature_upper S.curvature_half hab haOuter hbMargin
    S.noncritical S.critical_charge S.critical_rank S.distance_stable S.threshold_count S.rank_lower
  have hVS := mul_le_mul_of_nonneg_left hV hM
  have hIdentity : M*(Kv*W*(u^((9:ℝ)/10)*N+u^(1-nu/200))) = Ke*W*N*Eb := by
    have hP1 : u^((9:ℝ)/10)/u = u^(-(1:ℝ)/10) := by rw [rpow_div_self hu0]; norm_num
    have hP2 : u^(1-nu/200)/u = u^(-nu/200) := by rw [rpow_div_self hu0]; congr 1 <;> ring
    dsimp only [M,Ke,Eb]
    calc
      _ = 153600*splitCoefficient*Kv*W*N*((u^((9:ℝ)/10)/u)*N+u^(1-nu/200)/u) := by ring
      _ = _ := by rw [hP1,hP2] <;> ring
  change M*(∫ y in a..b, bandAvailabilityEnvelope κ B cap μ u (Real.log u/200) (fourPhaseDepth u+1) h y) ≤
    M*(Kv*W*(u^((9:ℝ)/10)*N+u^(1-nu/200))) at hVS
  rw [hIdentity] at hVS
  have hAi := bandAvailableKernelEnvelope_integrable (C:=C) (κ:=κ) (cap:=cap) (u:=u) (a:=a) (b:=b) h S.threshold_gt_one S.mu_positive S.curvature_half
  have hRi := bandRefinementSavings_weighted_integrable κ B μ u a b h
  have hVi := bandAvailabilityEnvelope_integrable κ B cap μ u (Real.log u/200) a b (fourPhaseDepth u+1) h
  have hEq : bandFullKernelEnvelope C κ B cap μ u h = fun y =>
      bandAvailableKernelEnvelope C κ B cap μ u h y+
        (2*splitCoefficient)*(Real.exp (nu*y)*bandRefinementSavings κ B μ u y h)+
        M*bandAvailabilityEnvelope κ B cap μ u (Real.log u/200) (fourPhaseDepth u+1) h y := by
    funext y
    unfold bandFullKernelEnvelope
    dsimp only [M,N]
    ring
  rw [hEq,intervalIntegral.integral_add (hAi.add (hRi.const_mul _)) (hVi.const_mul _),
    intervalIntegral.integral_add hAi (hRi.const_mul _),intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
  have hRaw : (∫ y in a..b, bandAvailableKernelEnvelope C κ B cap μ u h y)+
      (2*splitCoefficient)*(∫ y in a..b,Real.exp (nu*y)*bandRefinementSavings κ B μ u y h)+
      M*(∫ y in a..b, bandAvailabilityEnvelope κ B cap μ u (Real.log u/200) (fourPhaseDepth u+1) h y) ≤
      (Ka+Ks)*W+Ka*W*N*Ea+Ke*W*N*Eb := by
    dsimp only [Ks,W,N,Ea] at hA hS ⊢
    linear_combination hA+hS+hVS
  have hBase : Ka+Ks ≤ K := by dsimp only [K]; linarith only [hKe]
  have hALe : Ka ≤ K := by dsimp only [K]; linarith only [hKs,hKe]
  have hELe : Ke ≤ K := by dsimp only [K]; linarith only [hKa,hKs]
  apply hRaw.trans
  calc
    _ ≤ K*W+K*W*N*Ea+K*W*N*Eb := by gcongr
    _ = _ := by dsimp only [W,N,Ea,Eb,bandKernelError]; ring

end
end StrongSilver
