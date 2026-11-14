-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.WorkingLogEnvelope
import StrongSilver.RealPolylogMargins

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 3600000

/-- Normalized error when the full working cutoff is a fixed power
below the upper threshold. All parameters are fixed before schedules. -/
def workingPowerGapMargin (Cneg Ctail q σ τ υ A : ℝ) : ℝ :=
  (3/(1-nu)+34)*A^(-nu*q)+(152+6*Ctail)*A^(-nu*σ)*Real.log A+
    (154/(1-nu))*A^(-τ)*Real.log A+38000*Cneg*A^(-nu*υ)

theorem workingRankLogError_power_gap {A B cap μ σ τ υ q Cneg Ctail W critical : ℝ}
    (hA : 2 ≤ A) (he : Real.exp 1 ≤ A) (hlog : 1 ≤ Real.log A)
    (hB : 0 < B) (hgap : A^(1+q) ≤ B) (hBcap : B ≤ cap)
    (hμ : 0 ≤ μ) (hμB : μ*B ≤ 1/2) (hW : 0 ≤ W)
    (hCtail : 0 ≤ Ctail) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hcritical : critical ≤ 34*W*cap^(-nu)) :
    workingRankLogError Cneg Ctail A B μ σ τ υ W critical ≤
      W*A^(-nu)*workingPowerGapMargin Cneg Ctail q σ τ υ A := by
  have hA1 : 1 < A := lt_of_lt_of_le (by norm_num) hA
  have hA0 := zero_lt_one.trans hA1
  have hden : 0 < 1-nu := by linarith [nu_lt_one]
  have hcap0 := hB.trans_le hBcap
  have hBpow := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hA0 (1+q)) hgap (neg_nonpos.mpr nu_positive.le)
  rw [← Real.rpow_mul hA0.le] at hBpow
  have hBfactor : B^(-nu) ≤ A^(-nu)*A^(-nu*q) := by
    rw [← Real.rpow_add hA0]
    convert hBpow using 1 <;> congr 1 <;> ring
  have hBsplit : B^(1-nu) = B*B^(-nu) := by
    calc
      _ = B^(1:ℝ)*B^(-nu) := by
        rw [← Real.rpow_add hB]
        congr 1
      _ = _ := by rw [Real.rpow_one]
  have hmass : 6*μ*(W*B^(1-nu)/(1-nu)) ≤ (3/(1-nu))*W*A^(-nu)*A^(-nu*q) := by
    rw [hBsplit]
    calc
      _ = (6/(1-nu))*W*(μ*B)*B^(-nu) := by ring
      _ ≤ (3/(1-nu))*W*B^(-nu) := by
        have hh := mul_le_mul_of_nonneg_left hμB (show 0 ≤ (6/(1-nu))*W*B^(-nu) by positivity)
        linear_combination hh
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left hBfactor (show 0 ≤ (3/(1-nu))*W by positivity)
        linear_combination hh
  have hcrit : critical ≤ 34*W*A^(-nu)*A^(-nu*q) := by
    have hp := Real.rpow_le_rpow_of_nonpos hB hBcap (neg_nonpos.mpr nu_positive.le)
    have hh := mul_le_mul_of_nonneg_left (hp.trans hBfactor) (show 0 ≤ 34*W by positivity)
    linear_combination hcritical+hh
  have htail := mul_le_mul_of_nonneg_left (log_exp_add_power_le hA he hσ hσ1)
    (show 0 ≤ 2*Ctail*W*A^(-nu*(1+σ)) by positivity)
  have hτmass := mul_le_mul_of_nonneg_right
    (show 152*Real.log A+2 ≤ 154*Real.log A by linarith only [hlog])
    (show 0 ≤ W/(1-nu)*A^(-nu-τ) by positivity)
  rw [workingRankLogError_normal_form hA1]
  have hσpow : A^(-nu)*A^(-nu*σ) = A^(-nu*(1+σ)) := by
    rw [← Real.rpow_add hA0]
    congr 1
    ring
  have hτpow : A^(-nu)*A^(-τ) = A^(-nu-τ) := by
    rw [← Real.rpow_add hA0]
    congr 1
  have hυpow : A^(-nu)*A^(-nu*υ) = A^(-nu*(1+υ)) := by
    rw [← Real.rpow_add hA0]
    congr 1
    ring
  have hfinal : W*A^(-nu)*workingPowerGapMargin Cneg Ctail q σ τ υ A =
      (3/(1-nu)+34)*W*A^(-nu)*A^(-nu*q)+
      (152+6*Ctail)*W*A^(-nu*(1+σ))*Real.log A+
      (154/(1-nu))*W*A^(-nu-τ)*Real.log A+38000*Cneg*W*A^(-nu*(1+υ)) := by
    unfold workingPowerGapMargin
    calc
      _ = (3/(1-nu)+34)*W*A^(-nu)*A^(-nu*q)+
          (152+6*Ctail)*W*(A^(-nu)*A^(-nu*σ))*Real.log A+
          (154/(1-nu))*W*(A^(-nu)*A^(-τ))*Real.log A+
          38000*Cneg*W*(A^(-nu)*A^(-nu*υ)) := by ring
      _ = _ := by rw [hσpow,hτpow,hυpow]
  rw [hfinal]
  linear_combination hmass+hcrit+htail+hτmass

theorem eventually_workingPowerGapMargin_small {q σ τ υ : ℝ}
    (hq : 0 < q) (hσ : 0 < σ) (hτ : 0 < τ) (hυ : 0 < υ) (Cneg Ctail : ℝ) :
    ∀ᶠ A : ℝ in atTop, workingPowerGapMargin Cneg Ctail q σ τ υ A ≤ 1/Real.log A := by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    eventually_const_mul_log_rpow_mul_power_le_inverse_log 0 (4*(3/(1-nu)+34)) (neg_neg_of_pos (mul_pos nu_positive hq)),
    eventually_const_mul_log_rpow_mul_power_le_inverse_log 1 (4*(152+6*Ctail)) (neg_neg_of_pos (mul_pos nu_positive hσ)),
    eventually_const_mul_log_rpow_mul_power_le_inverse_log 1 (4*(154/(1-nu))) (neg_neg_of_pos hτ),
    eventually_const_mul_log_rpow_mul_power_le_inverse_log 0 (4*(38000*Cneg)) (neg_neg_of_pos (mul_pos nu_positive hυ))]
    with A hA h1 h2 h3 h4
  simp only [Real.rpow_zero,Real.rpow_one,mul_one] at h1 h2 h3 h4
  unfold workingPowerGapMargin
  simp only [neg_mul]
  nlinarith only [h1,h2,h3,h4]

end
end StrongSilver
