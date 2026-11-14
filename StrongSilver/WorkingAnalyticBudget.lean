-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PhaseGapProducts

namespace StrongSilver.LocalPhaseCertificate
open Real
noncomputable section
variable {A μ b T e : ℝ} {h : List ℝ} (L : LocalPhaseCertificate A μ b T e h)
include L
set_option maxHeartbeats 1000000

theorem working_curvature_cap (hAT : A/T ≤ 1/2) (hμT : μ*T ≤ 31/32) : μ*A ≤ 1/2 := by
  have ha := (div_le_iff₀ L.T_positive).mp hAT
  have hm := mul_le_mul_of_nonneg_left ha L.mu_positive.le
  nlinarith only [hm,hμT]

theorem working_gap_max_bound (hAT : A/T ≤ 1/2) (hμT : μ*T ≤ 31/32) :
    transformedGapMaximum μ h ≤ 2*Scalar.SignedIntervals.positiveMass h := by
  have hcap := L.working_curvature_cap hAT hμT
  have hcap1 : μ*A < 1 := by linarith
  have hm := transformedGapMaximum_le_positive_mass L.mu_positive hcap1 h L.gap_cap
  have hS := Scalar.SignedIntervals.positiveMass_nonneg h
  have hfrac : Scalar.SignedIntervals.positiveMass h/(1-μ*A) ≤ 2*Scalar.SignedIntervals.positiveMass h := by
    apply (div_le_iff₀ (by linarith : 0 < 1-μ*A)).mpr
    have hh := mul_nonneg hS (show 0 ≤ 1/2-μ*A by linarith)
    nlinarith only [hh]
  exact hm.trans hfrac

theorem working_gap_exponent_bound (hAT : A/T ≤ 1/2) (hμT : μ*T ≤ 31/32)
    (hST : Scalar.SignedIntervals.positiveMass h/T ≤ 2) : μ*transformedGapMaximum μ h ≤ 4 := by
  have hm := mul_le_mul_of_nonneg_left (L.working_gap_max_bound hAT hμT) L.mu_positive.le
  have hS := (div_le_iff₀ L.T_positive).mp hST
  have hμS := mul_le_mul_of_nonneg_left hS L.mu_positive.le
  nlinarith only [hm,hμS,hμT]

theorem working_growth_bound (hA : 1 ≤ A) (hAT : A/T ≤ 1/2)
    (hST : Scalar.SignedIntervals.positiveMass h/T ≤ 2)
    (hSb : Scalar.SignedIntervals.positiveMass h/b ≤ A^((3 : ℝ)/1000)) :
    scalarRampGrowth T A b h ≤ (2*Real.exp 4)*A^((3 : ℝ)/1000) := by
  have hden : 0 < T*(1-A/T) := mul_pos L.T_positive (by linarith)
  have hS := (div_le_iff₀ L.T_positive).mp hST
  have hhalf := (div_le_iff₀ L.T_positive).mp hAT
  have hratio : Scalar.SignedIntervals.positiveMass h/(T*(1-A/T)) ≤ 4 := by
    apply (div_le_iff₀ hden).mpr
    have he : T*(1-A/T) = T-A := by field_simp [L.T_positive.ne'] <;> ring
    rw [he]
    linarith only [hS,hhalf]
  have hexp := Real.exp_le_exp.mpr hratio
  have hpow : 1 ≤ A^((3 : ℝ)/1000) := Real.one_le_rpow hA (by norm_num)
  have hfactor : 1+Scalar.SignedIntervals.positiveMass h/b ≤ 2*A^((3 : ℝ)/1000) := by linarith
  have hfactor0 : 0 ≤ 1+Scalar.SignedIntervals.positiveMass h/b :=
    add_nonneg zero_le_one (div_nonneg (Scalar.SignedIntervals.positiveMass_nonneg h) L.b_positive.le)
  have hm := mul_le_mul hexp hfactor hfactor0 (Real.exp_pos 4).le
  unfold scalarRampGrowth
  nlinarith only [hm]

theorem working_q_lower (hAT : A/T ≤ 1/2) (hμT : μ*T ≤ 31/32)
    (hST : Scalar.SignedIntervals.positiveMass h/T ≤ 2) :
    1/(32*Real.exp 4) ≤ quadraticMultiplier μ h*(1-μ*b) := by
  have hexp := L.working_gap_exponent_bound hAT hμT hST
  have hc : minPrefixProduct μ h = Real.exp (-μ*transformedGapMaximum μ h) := by
    rw [neg_mul,Real.exp_neg,transformedGapMaximum_exp L.mu_positive h L.small_steps,inv_inv]
  have hmin : Real.exp (-4) ≤ minPrefixProduct μ h := by
    rw [hc]
    exact Real.exp_le_exp.mpr (by linarith only [hexp])
  have hfull := hmin.trans (minPrefixProduct_le_full h L.small_steps)
  have hbμ := mul_le_mul_of_nonneg_left L.b_lt_T.le L.mu_positive.le
  have hselected : (1 : ℝ)/32 ≤ 1-μ*b := by linarith only [hbμ,hμT]
  have hp := mul_le_mul hfull hselected (by norm_num : (0 : ℝ) ≤ 1/32) (quadraticMultiplier_positive h L.small_steps).le
  have he : Real.exp (-4)*((1 : ℝ)/32) = 1/(32*Real.exp 4) := by
    rw [Real.exp_neg]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rwa [he] at hp

end
end StrongSilver.LocalPhaseCertificate
