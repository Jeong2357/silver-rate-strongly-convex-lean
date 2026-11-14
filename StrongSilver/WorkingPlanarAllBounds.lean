-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.SmallStepInverseCharge
import StrongSilver.WorkingAnalyticBudget
import StrongSilver.LocalPhaseAbsoluteBounds
import StrongSilver.PowerMargins

namespace StrongSilver.LocalPhaseCertificate
open Real Filter Complex
noncomputable section
variable {A μ b T e : ℝ} {h : List ℝ} (L : LocalPhaseCertificate A μ b T e h)
include L
set_option maxHeartbeats 1600000

theorem terminal_planar_norm_le_two : ‖(⟨planarEpsilon A,1⟩ : ℂ)‖ ≤ 2 := by
  have hh := Complex.norm_le_abs_re_add_abs_im (⟨planarEpsilon A,1⟩ : ℂ)
  simp only [abs_of_pos L.planar.epsilon_pos,abs_one] at hh
  linarith only [hh,L.planar.epsilon_slope,L.planar.scale_le]

theorem planar_all_norm_bound (hAT : A/T ≤ 1/2) (hμT : μ*T ≤ 31/32)
    (hST : Scalar.SignedIntervals.positiveMass h/T ≤ 2) (i : ℕ) :
    ‖iterate (h.take i) L.planar.physical L.R‖ ≤
      Real.exp 4*(2+2*Scalar.SignedIntervals.positiveMass h) := by
  have hr0 : planarRadius A 0 ≤ 2 := by linarith [L.planar.head_radius_bound,L.planar.scale_le]
  have hcharge := inverseCharge_small_steps L.mu_positive.le (L.working_curvature_cap hAT hμT) h L.gap_cap
  have hmass := (div_le_iff₀ L.T_positive).mp hST
  have hμmass := mul_le_mul_of_nonneg_left hmass L.mu_positive.le
  have hcharge4 : inverseCharge μ h ≤ 4 := by nlinarith only [hcharge,hμmass,hμT]
  have hgrad (z : ℂ) : ‖Moreau.gradient L.planar.body.supportEpigraph z‖ ≤ planarRadius A 0 := by
    rw [L.planar.body.support_envelope_gradient]
    exact L.planar.body_norm_bound (L.planar.body.projection_mem z)
  have hh := backward_norm_all_prefixes L.mu_positive L.planar.mu_lt_one.le (L.planar.radius_pos 0).le
    (Moreau.gradient L.planar.body.supportEpigraph) (Moreau.gradient_inner_nonnegative _)
    hgrad h (fun t ht => by linarith [L.small_steps t ht]) L.R _ L.planar_run i
  have hs := smallPositiveSum_le_positiveMass μ h
  have hc : 0 ≤ (1-μ)*planarRadius A 0 := mul_nonneg (sub_nonneg.mpr L.planar.mu_lt_one.le) (L.planar.radius_pos 0).le
  have hc2 : (1-μ)*planarRadius A 0 ≤ 2 := by
    nlinarith only [hr0,mul_nonneg L.mu_positive.le (L.planar.radius_pos 0).le]
  have h1 := mul_le_mul_of_nonneg_right hc2 (smallPositiveSum_nonneg μ h)
  have hbracket : ‖(⟨planarEpsilon A,1⟩ : ℂ)‖+(1-μ)*planarRadius A 0*smallPositiveSum μ h ≤
      2+2*Scalar.SignedIntervals.positiveMass h := by nlinarith only [h1,hs,L.terminal_planar_norm_le_two]
  exact hh.trans (mul_le_mul (Real.exp_le_exp.mpr hcharge4) hbracket
    (add_nonneg (norm_nonneg _) (mul_nonneg hc (smallPositiveSum_nonneg μ h))) (Real.exp_pos _).le)

end
end StrongSilver.LocalPhaseCertificate

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 1000000

theorem eventually_working_planar_all_power : ∀ᶠ A : ℝ in atTop,
    ∀ μ b T e : ℝ, ∀ h : List ℝ, ∀ L : LocalPhaseCertificate A μ b T e h,
      A/T ≤ 1/2 → μ*T ≤ 31/32 → Scalar.SignedIntervals.positiveMass h/T ≤ 2 →
      Scalar.SignedIntervals.positiveMass h ≤ A^((1003 : ℝ)/1000) →
      ∀ i : ℕ, ‖iterate (h.take i) L.planar.physical L.R‖ ≤ A^(3 : ℝ) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),eventually_const_mul_power_le (by norm_num : (2 : ℝ) < 3) (4*Real.exp 4)]
    with A hA hpow
  intro μ b T e h L hAT hμT hST hS i
  have hA2 : 1 ≤ A^(2 : ℝ) := Real.one_le_rpow hA (by norm_num)
  have hmass : Scalar.SignedIntervals.positiveMass h ≤ A^(2 : ℝ) :=
    hS.trans (Real.rpow_le_rpow_of_exponent_le hA (by norm_num))
  have hh := L.planar_all_norm_bound hAT hμT hST i
  have hscale := mul_le_mul_of_nonneg_left (show 2+2*Scalar.SignedIntervals.positiveMass h ≤ 4*A^(2 : ℝ) by linarith)
    (Real.exp_pos 4).le
  exact hh.trans ((by nlinarith only [hscale] : Real.exp 4*(2+2*Scalar.SignedIntervals.positiveMass h) ≤
    (4*Real.exp 4)*A^(2 : ℝ)).trans hpow)

end
end StrongSilver
