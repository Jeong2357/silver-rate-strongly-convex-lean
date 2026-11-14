-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.WorkingLogEnvelope
import StrongSilver.FarCutoffBounds

namespace StrongSilver
open Real Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 2400000

def farScaledLogEnvelope (Cneg Ctail σ τ υ ξ ε a B : ℝ) : ℝ :=
  (12/(1-nu))*B^(-ε/(1-ε))+
    (152+6*Ctail)*B^(nu+(1-ξ)*(-nu*(1+σ)))*Real.log B+
    (154/(1-nu))*B^(nu+(1-ξ)*(-nu-τ))*Real.log B+
    38000*Cneg*B^(nu+(1-ξ)*(-nu*(1+υ)))+
    34*a^(-nu)*B^((-ε/(1-ε))*nu)

theorem scaled_workingLogEnvelope_identity {B κ a : ℝ} (hB : 0 < B) (hκ : 0 < κ) (ha : 0 < a)
    (Cneg Ctail σ τ υ ξ W : ℝ) :
    B^nu*workingLogEnvelope Cneg Ctail (B^(1-ξ)) B (9/(8*κ)) σ τ υ W (34*W*(a*κ)^(-nu)) =
      W*(6*(9/(8*κ))*B/(1-nu)+
        (152+6*Ctail)*B^(nu+(1-ξ)*(-nu*(1+σ)))*Real.log B+
        (154/(1-nu))*B^(nu+(1-ξ)*(-nu-τ))*Real.log B+
        38000*Cneg*B^(nu+(1-ξ)*(-nu*(1+υ)))+34*a^(-nu)*(B/κ)^nu) := by
  have hprod (r : ℝ) : B^nu*(B^(1-ξ))^r = B^(nu+(1-ξ)*r) := by
    rw [← Real.rpow_mul hB.le,← Real.rpow_add hB]
  have hmass : B^nu*B^(1-nu) = B := by
    rw [← Real.rpow_add hB,show nu+(1-nu) = (1 : ℝ) by ring,Real.rpow_one]
  have hcap : B^nu*(a*κ)^(-nu) = a^(-nu)*(B/κ)^nu := by
    rw [Real.mul_rpow ha.le hκ.le,Real.div_rpow hB.le hκ.le,Real.rpow_neg hκ.le]
    ring
  unfold workingLogEnvelope
  calc
    _ = W*(6*(9/(8*κ))*(B^nu*B^(1-nu))/(1-nu)+
        (152+6*Ctail)*(B^nu*(B^(1-ξ))^(-nu*(1+σ)))*Real.log B+
        (154/(1-nu))*(B^nu*(B^(1-ξ))^(-nu-τ))*Real.log B+
        38000*Cneg*(B^nu*(B^(1-ξ))^(-nu*(1+υ)))+34*(B^nu*(a*κ)^(-nu))) := by ring
    _ = _ := by rw [hmass,hprod,hprod,hprod,hcap]; ring

theorem scaled_workingLogEnvelope_far_bound {B κ a ε : ℝ} (hB : 0 < B) (hκ : 0 < κ) (ha : 0 < a)
    (hε : ε < 1) (hfar : B ≤ κ^(1-ε)) (Cneg Ctail σ τ υ ξ : ℝ) {W : ℝ} (hW : 0 ≤ W) :
    B^nu*workingLogEnvelope Cneg Ctail (B^(1-ξ)) B (9/(8*κ)) σ τ υ W (34*W*(a*κ)^(-nu)) ≤
      W*farScaledLogEnvelope Cneg Ctail σ τ υ ξ ε a B := by
  have hd : 0 < 1-nu := by linarith [nu_lt_one]
  have hr := far_cutoff_ratio_bound hB hκ hε hfar
  have hμ : 9/(8*κ) ≤ 2/κ := by
    apply (div_le_div_iff₀ (by positivity : 0 < 8*κ) hκ).mpr
    nlinarith only [hκ]
  have hcurv : 6*(9/(8*κ))*B/(1-nu) ≤ (12/(1-nu))*B^(-ε/(1-ε)) := by
    calc
      _ ≤ 6*(2/κ)*B/(1-nu) := by gcongr
      _ = (12/(1-nu))*(B/κ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hr (by positivity)
  have hpow := Real.rpow_le_rpow (div_nonneg hB.le hκ.le) hr nu_positive.le
  rw [← Real.rpow_mul hB.le] at hpow
  have hcrit := mul_le_mul_of_nonneg_left hpow (show 0 ≤ 34*a^(-nu) by positivity)
  rw [scaled_workingLogEnvelope_identity hB hκ ha]
  apply mul_le_mul_of_nonneg_left _ hW
  unfold farScaledLogEnvelope
  linear_combination hcurv+hcrit

theorem tendsto_farScaledLogEnvelope {σ τ υ ξ ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hσ : nu+(1-ξ)*(-nu*(1+σ)) < 0) (hτ : nu+(1-ξ)*(-nu-τ) < 0)
    (hυ : nu+(1-ξ)*(-nu*(1+υ)) < 0) (Cneg Ctail a : ℝ) :
    Tendsto (farScaledLogEnvelope Cneg Ctail σ τ υ ξ ε a) atTop (𝓝 0) := by
  have hd := div_pos hε (sub_pos.mpr hε1)
  have h1 : Tendsto (fun B : ℝ => B^(-ε/(1-ε))) atTop (𝓝 0) := by
    simpa only [neg_div] using tendsto_rpow_neg_atTop hd
  have h2 := tendsto_negative_rpow_mul_log hσ
  have h3 := tendsto_negative_rpow_mul_log hτ
  have h4 : Tendsto (fun B : ℝ => B^(nu+(1-ξ)*(-nu*(1+υ)))) atTop (𝓝 0) :=
    by simpa only [neg_neg] using tendsto_rpow_neg_atTop (neg_pos.mpr hυ)
  have h5 : Tendsto (fun B : ℝ => B^((-ε/(1-ε))*nu)) atTop (𝓝 0) := by
    have hh : 0 < -((-ε/(1-ε))*nu) := by
      simpa only [neg_div,neg_mul,neg_neg] using mul_pos hd nu_positive
    simpa only [neg_neg] using tendsto_rpow_neg_atTop hh
  have hh := ((((h1.const_mul (12/(1-nu))).add (h2.const_mul (152+6*Ctail))).add
    (h3.const_mul (154/(1-nu)))).add (h4.const_mul (38000*Cneg))).add (h5.const_mul (34*a^(-nu)))
  simp only [mul_zero,add_zero] at hh
  apply hh.congr'
  exact Filter.Eventually.of_forall (fun B => by unfold farScaledLogEnvelope; ring)

end
end StrongSilver
