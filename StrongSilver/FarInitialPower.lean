-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.WorkingPowerForCurvature
import StrongSilver.FarPowerAbsorption
import StrongSilver.InitialBandLogCharge

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 3000000

/-- The far-cutoff branch of the first-threshold power bound, retaining
its common pad and terminal reserve. No logarithmic or DP construction
hypothesis is assumed: stability is the actual last-iterate error bound. -/
theorem eventually_far_initial_padded_power {a σ τ υ ξ ε : ℝ} (ha : 0 < a) (hamax : a ≤ 1/128)
    (hσ : 0 < σ) (hσmax : σ ≤ 1/200) (hτ : 0 < τ) (hτmax : τ ≤ 1/1000)
    (hσυ : σ < υ) (hτυ : τ < υ) (hυmax : υ ≤ 1/50)
    (hξ : 0 < ξ) (hξmax : ξ ≤ 1/1000) (hε : 0 < ε) (hε1 : ε < 1)
    (hsep : (1-ε)*(1+υ) < 1)
    (hσdecay : nu+(1-ξ)*(-nu*(1+σ)) < 0) (hτdecay : nu+(1-ξ)*(-nu-τ) < 0)
    (hυdecay : nu+(1-ξ)*(-nu*(1+υ)) < 0)
    (hcount : splitCoefficient*((4800/(1-ξ))*ξ) < powerLogMinimum/4) :
    ∀ᶠ B : ℝ in atTop, ∀ κ : ℝ, ∀ h : List ℝ,
      1 < κ → B ≤ a*κ → B ≤ κ^(1-ε) →
      weightedCount h (a*κ) = (countAbove h B : ℝ)*B^nu → D κ h ≤ 1 →
      ∃ μ : ℝ, 1/κ ≤ μ ∧ μ ≤ 9/(8*κ) ∧ (∀ b ∈ h, 1-μ*b ≠ 0) ∧
        inverseChargeAbove (κ/4) h μ ≤ 34*(countAbove h (κ/4) : ℝ) ∧
        ∀ A : ℝ, B^(1-ξ) ≤ A → A < B → (powerLogMinimum/4)*weightedCount h (a*κ) ≤
          cutPower (cappedStep μ B) (B^((987 : ℝ)/1000)) κ (fullCut A h) := by
  obtain ⟨Cneg,hCneg,Ctail,hCtail,hfinite⟩ := eventually_working_power_for_curvature hσ hσmax hτ hτmax hσυ hτυ hυmax
  have hξ1 : ξ < 1 := hξmax.trans_lt (by norm_num)
  have hfloorEscape := tendsto_rpow_atTop (sub_pos.mpr hξ1)
  filter_upwards [hfloorEscape.eventually (eventually_all_larger hfinite),
    hfloorEscape.eventually (eventually_ge_atTop (4 : ℝ)),eventually_gt_atTop (1 : ℝ),
    eventually_initial_band_pad_margin hξmax,eventually_far_cutoff_time ha hε1 hsep,
    eventually_farPowerLoss_small hε hε1 hσdecay hτdecay hυdecay hcount Cneg Ctail a]
    with B hfactory hfloor4 hB1 hmargin htime hsmall
  intro κ h hκ hBcap hfar hmax hD
  have hB0 := zero_lt_one.trans hB1
  have hκ0 := zero_lt_one.trans hκ
  obtain ⟨μ,hμ,hμu,hcrit,_,hquarter⟩ := exists_common_curvature_with_quarter_bound hκ0 h
  refine ⟨μ,hμ,hμu,hcrit,hquarter,?_⟩
  intro A hfloor hAB
  have hfloor0 := Real.rpow_pos_of_pos hB0 (1-ξ)
  have hA0 := hfloor0.trans_le hfloor
  have hcapκ : a*κ ≤ κ/4 := by
    have hh := mul_le_mul_of_nonneg_right hamax hκ0.le
    nlinarith only [hh,hκ0]
  have hpad : ∀ t : ℝ, A ≤ t → t ≤ B → t^((49 : ℝ)/50) ≤ B^((987 : ℝ)/1000) ∧
      B^((987 : ℝ)/1000) ≤ t^((199 : ℝ)/200) :=
    fun t hAt htB => initial_band_pad_bounds hB1.le hξ.le hξmax (hfloor.trans hAt) htB
  have hpower := hfactory A hfloor κ B (a*κ) (B^((987 : ℝ)/1000)) μ h hκ hAB hBcap hcapκ
    (htime κ hκ0 hfar) hpad (hmargin.trans hfloor) hmax hD hμ hμu hcrit hquarter
  let W := weightedCount h (a*κ)
  let critical := 34*W*(a*κ)^(-nu)
  have hW : 0 ≤ W := weightedCount_nonneg h (a*κ)
  have henv := workingLogEnvelope_mono_cutoff (Cneg := Cneg) (Ctail := Ctail) (μ := 9/(8*κ))
    (critical := critical) hfloor0 hfloor hB1.le hCneg.le hCtail.le hW hσ.le hτ.le (hσ.trans hσυ).le
  have henvScaled := mul_le_mul_of_nonneg_left henv (Real.rpow_pos_of_pos hB0 nu).le
  have hfarScaled := scaled_workingLogEnvelope_far_bound hB0 hκ0 ha hε1 hfar Cneg Ctail σ τ υ ξ hW
  have hcost := henvScaled.trans hfarScaled
  have hlogCharge := initial_band_selected_log_charge hB1 hξ1 hfloor hAB.le
  have hcharge := mul_le_mul_of_nonneg_left hlogCharge (show 0 ≤ 4*W by positivity)
  have hcombined : splitCoefficient*(2*workingLogEnvelope Cneg Ctail A B (9/(8*κ)) σ τ υ W critical*B^nu+
      4*(1200/Real.log A)*W*(1+Real.log (B/A))) ≤ W*farPowerLoss Cneg Ctail σ τ υ ξ ε a B := by
    unfold farPowerLoss
    have hc := split_coefficient_positive
    linear_combination (2*splitCoefficient)*hcost+splitCoefficient*hcharge
  have htotal : W*farPowerLoss Cneg Ctail σ τ υ ξ ε a B ≤ W*(powerLogMinimum/4) :=
    mul_le_mul_of_nonneg_left hsmall hW
  change (powerLogMinimum/2)*W-splitCoefficient*(2*workingLogEnvelope Cneg Ctail A B (9/(8*κ)) σ τ υ W critical*B^nu+
      4*(1200/Real.log A)*W*(1+Real.log (B/A))) ≤ _ at hpower
  linear_combination hpower+hcombined+htotal

end
end StrongSilver
