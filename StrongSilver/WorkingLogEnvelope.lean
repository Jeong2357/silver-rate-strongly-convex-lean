-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.WorkingStableRankLog

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 2400000

theorem log_exp_add_power_le {A s : ℝ} (hA : 2 ≤ A) (he : Real.exp 1 ≤ A)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) : Real.log (Real.exp 1+A^(1+s)) ≤ 3*Real.log A := by
  have hA0 : 0 < A := lt_of_lt_of_le (by norm_num) hA
  have hA1 : 1 ≤ A := le_trans (by norm_num) hA
  have hpow : A ≤ A^(1+s) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hA1 (show (1 : ℝ) ≤ 1+s by linarith only [hs])
  have hp := Real.rpow_pos_of_pos hA0 (1+s)
  have hh := Real.log_le_log (by positivity : 0 < Real.exp 1+A^(1+s))
    (show Real.exp 1+A^(1+s) ≤ 2*A^(1+s) by linarith only [he,hpow])
  rw [Real.log_mul (by norm_num) hp.ne',Real.log_rpow hA0] at hh
  have htwo := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hA
  have hlog := Real.log_nonneg hA1
  have hmul := mul_nonneg (sub_nonneg.mpr hs1) hlog
  nlinarith only [hh,htwo,hmul]

def workingLogEnvelope (Cneg Ctail A B μ σ τ υ W critical : ℝ) : ℝ :=
  6*μ*(W*B^(1-nu)/(1-nu))+
    (152+6*Ctail)*W*A^(-nu*(1+σ))*Real.log B+
    (154/(1-nu))*W*A^(-nu-τ)*Real.log B+
    38000*Cneg*W*A^(-nu*(1+υ))+critical

theorem workingRankLogError_normal_form {A : ℝ} (hA : 1 < A) (Cneg Ctail B μ σ τ υ W critical : ℝ) :
    workingRankLogError Cneg Ctail A B μ σ τ υ W critical =
      6*μ*(W*B^(1-nu)/(1-nu))+
      152*W*A^(-nu*(1+σ))*Real.log A+
      (152*Real.log A+2)*(W/(1-nu)*A^(-nu-τ))+
      38000*Cneg*W*A^(-nu*(1+υ))+critical+
      2*Ctail*W*A^(-nu*(1+σ))*Real.log (Real.exp 1+A^(1+σ)) := by
  have hA0 := zero_lt_one.trans hA
  have hlog := (Real.log_pos hA).ne'
  have hσpow : (A^(1+σ))^(-nu) = A^(-nu*(1+σ)) := by rw [← Real.rpow_mul hA0.le]; congr 1; ring
  have hυpow : (A^(1+υ))^(-nu) = A^(-nu*(1+υ)) := by rw [← Real.rpow_mul hA0.le]; congr 1; ring
  have hmass : (W*A^(1-nu)/(1-nu))/A^(1+τ) = W/(1-nu)*A^(-nu-τ) := by
    calc
      _ = W/(1-nu)*(A^(1-nu)/A^(1+τ)) := by ring
      _ = _ := by rw [← Real.rpow_sub hA0]; congr 2; ring
  have hmass2 : 2*(W*A^(1-nu)/(1-nu))/A^(1+τ) = 2*(W/(1-nu)*A^(-nu-τ)) := by
    calc
      _ = 2*((W*A^(1-nu)/(1-nu))/A^(1+τ)) := by ring
      _ = _ := by rw [hmass]
  unfold workingRankLogError
  simp only [hσpow,hυpow,hmass,hmass2]
  field_simp
  <;> ring

theorem workingRankLogError_le_envelope {A B Cneg Ctail μ σ τ υ W critical : ℝ}
    (hA : 2 ≤ A) (he : Real.exp 1 ≤ A) (hlog : 1 ≤ Real.log A) (hAB : A ≤ B)
    (hCtail : 0 ≤ Ctail) (hW : 0 ≤ W) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    workingRankLogError Cneg Ctail A B μ σ τ υ W critical ≤
      workingLogEnvelope Cneg Ctail A B μ σ τ υ W critical := by
  have hden : 0 < 1-nu := by linarith [nu_lt_one]
  have hA1 : 1 < A := lt_of_lt_of_le (by norm_num) hA
  have hA0 := zero_lt_one.trans hA1
  have hlogs := Real.log_le_log hA0 hAB
  have htail := log_exp_add_power_le hA he hσ hσ1
  have hpσ : 0 ≤ W*A^(-nu*(1+σ)) := mul_nonneg hW (Real.rpow_pos_of_pos hA0 _).le
  have hpτ : 0 ≤ W/(1-nu)*A^(-nu-τ) := by
    exact mul_nonneg (div_nonneg hW (by linarith [nu_lt_one] : 0 ≤ 1-nu)) (Real.rpow_pos_of_pos hA0 _).le
  have ht := mul_le_mul_of_nonneg_left htail (show 0 ≤ 2*Ctail*W*A^(-nu*(1+σ)) by positivity)
  have hlσ := mul_le_mul_of_nonneg_left hlogs (show 0 ≤ (152+6*Ctail)*W*A^(-nu*(1+σ)) by positivity)
  have hlτ := mul_le_mul_of_nonneg_left hlogs (show 0 ≤ (154/(1-nu))*W*A^(-nu-τ) by positivity)
  have hm := mul_le_mul_of_nonneg_right (show 152*Real.log A+2 ≤ 154*Real.log A by linarith only [hlog]) hpτ
  rw [workingRankLogError_normal_form hA1]
  unfold workingLogEnvelope
  linear_combination ht+hlσ+hlτ+hm

/-- A single lower cutoff controls every intermediate cutoff in a finite
refinement chain. Only the harmless logarithm uses the upper cutoff B. -/
theorem workingLogEnvelope_mono_cutoff {A t B Cneg Ctail μ σ τ υ W critical : ℝ}
    (hA : 0 < A) (hAt : A ≤ t) (hB : 1 ≤ B) (hCneg : 0 ≤ Cneg) (hCtail : 0 ≤ Ctail)
    (hW : 0 ≤ W) (hσ : 0 ≤ σ) (hτ : 0 ≤ τ) (hυ : 0 ≤ υ) :
    workingLogEnvelope Cneg Ctail t B μ σ τ υ W critical ≤
      workingLogEnvelope Cneg Ctail A B μ σ τ υ W critical := by
  have hden : 0 < 1-nu := by linarith [nu_lt_one]
  have hs : t^(-nu*(1+σ)) ≤ A^(-nu*(1+σ)) :=
    Real.rpow_le_rpow_of_nonpos hA hAt (by have hh := mul_nonneg nu_positive.le (show 0 ≤ 1+σ by linarith only [hσ]); linarith only [hh])
  have ht : t^(-nu-τ) ≤ A^(-nu-τ) := Real.rpow_le_rpow_of_nonpos hA hAt (by linarith [nu_positive])
  have hu : t^(-nu*(1+υ)) ≤ A^(-nu*(1+υ)) :=
    Real.rpow_le_rpow_of_nonpos hA hAt (by have hh := mul_nonneg nu_positive.le (show 0 ≤ 1+υ by linarith only [hυ]); linarith only [hh])
  have hlog := Real.log_nonneg hB
  have hs' := mul_le_mul_of_nonneg_left hs (show 0 ≤ (152+6*Ctail)*W*Real.log B by positivity)
  have ht' := mul_le_mul_of_nonneg_left ht (show 0 ≤ (154/(1-nu))*W*Real.log B by positivity)
  have hu' := mul_le_mul_of_nonneg_left hu (show 0 ≤ 38000*Cneg*W by positivity)
  unfold workingLogEnvelope
  linear_combination hs'+ht'+hu'

end
end StrongSilver
