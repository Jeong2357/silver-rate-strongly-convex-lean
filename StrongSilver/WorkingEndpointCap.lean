-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.WorkingPlanarAllBounds

namespace StrongSilver.LocalPhaseCertificate
open Real Complex
noncomputable section
variable {A μ b T e : ℝ} {h : List ℝ} (L : LocalPhaseCertificate A μ b T e h)
include L
set_option maxHeartbeats 1200000

theorem endpointProximalCap_le {B : ℝ} (hB : 0 ≤ B) :
    L.endpointProximalCap B ≤ ‖(⟨planarEpsilon A,1⟩ : ℂ)‖*B+L.terminalInner*Real.exp (negativeLogSum h T) := by
  unfold endpointProximalCap
  apply (div_le_iff₀ (norm_pos_iff.mpr L.endpoint_ne_zero)).mpr
  have hQ : 0 ≤ ‖(⟨planarEpsilon A,1⟩ : ℂ)‖*B+L.terminalInner*Real.exp (negativeLogSum h T) :=
    add_nonneg (mul_nonneg (norm_nonneg _) hB) (mul_nonneg L.terminalInner_nonnegative (Real.exp_pos _).le)
  have hh := mul_le_mul_of_nonneg_right L.endpoint_norm_lower hQ
  nlinarith only [hh]

theorem endpointProximalCap_power_bound (hR : ‖L.R‖ ≤ A^(3 : ℝ))
    (hE : negativeLogSum h T ≤ (1/250)*Real.log A) :
    L.endpointProximalCap (A^(3 : ℝ)) ≤ 4*A^(4 : ℝ) := by
  have hA : 1 ≤ A := L.planar.large.le
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  have hB0 : 0 ≤ A^(3 : ℝ) := (Real.rpow_pos_of_pos hA0 _).le
  have hJ := (real_inner_le_norm L.R (⟨planarEpsilon A,1⟩ : ℂ)).trans
    (mul_le_mul hR L.terminal_planar_norm_le_two (norm_nonneg _) hB0)
  have hExp : Real.exp (negativeLogSum h T) ≤ A := by
    rw [← Real.exp_log hA0]
    apply Real.exp_le_exp.mpr
    nlinarith only [hE,Real.log_nonneg hA]
  have h1 := mul_le_mul_of_nonneg_right L.terminal_planar_norm_le_two hB0
  have h2 := mul_le_mul hJ hExp (Real.exp_pos _).le (by positivity : 0 ≤ A^(3 : ℝ)*2)
  change L.terminalInner*Real.exp (negativeLogSum h T) ≤ A^(3 : ℝ)*2*A at h2
  have h3 := mul_le_mul_of_nonneg_left hA hB0
  have hp : A^(3 : ℝ)*A = A^(4 : ℝ) := by
    calc
      _ = A^(3 : ℝ)*A^(1 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hA0]; norm_num
  have hcap := L.endpointProximalCap_le hB0
  change L.terminalInner ≤ A^(3 : ℝ)*2 at hJ
  rw [hp] at h3
  have h2' : L.terminalInner*Real.exp (negativeLogSum h T) ≤ 2*A^(4 : ℝ) := by
    calc
      _ ≤ A^(3 : ℝ)*2*A := h2
      _ = 2*(A^(3 : ℝ)*A) := by ring
      _ = _ := by rw [hp]
  linarith only [hcap,h1,h2',h3]

end
end StrongSilver.LocalPhaseCertificate

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 1000000

theorem eventually_working_endpoint_cap : ∀ᶠ A : ℝ in atTop,
    ∀ μ b T e : ℝ, ∀ h : List ℝ, ∀ L : LocalPhaseCertificate A μ b T e h,
      A/T ≤ 1/2 → μ*T ≤ 31/32 → Scalar.SignedIntervals.positiveMass h/T ≤ 2 →
      Scalar.SignedIntervals.positiveMass h ≤ A^((1003 : ℝ)/1000) →
      negativeLogSum h T ≤ (1/250)*Real.log A → L.endpointProximalCap (A^(3 : ℝ)) ≤ A^(5 : ℝ) := by
  filter_upwards [eventually_working_planar_all_power,
    eventually_const_mul_power_le (by norm_num : (4 : ℝ) < 5) 4] with A hR hpow
  intro μ b T e h L hAT hμT hST hS hE
  have hR0 : ‖L.R‖ ≤ A^(3 : ℝ) := by
    simpa only [List.take_zero,iterate_nil] using hR μ b T e h L hAT hμT hST hS 0
  exact (L.endpointProximalCap_power_bound hR0 hE).trans hpow

end
end StrongSilver
