-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ConeSizeBounds
import StrongSilver.ConeLocalTrajectory
import StrongSilver.WorkingNewGate

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 2000000

theorem eventually_working_cone_size : ∀ᶠ A : ℝ in atTop,
    ∀ μ b V : ℝ, 0 ≤ μ → 1 ≤ b → b ≤ A^(2 : ℝ) → 0 < V → 1/32 ≤ 1-μ*b →
      ∀ C : ConeConnectorParameters μ b V (A^(10 : ℝ)) (A^(10 : ℝ)*V) (workingGateFraction A),
        C.U ≤ A^(14 : ℝ)*V ∧ 2*C.a ≤ A^(14 : ℝ)*V := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    eventually_const_mul_power_le (by norm_num : (12 : ℝ) < 13) 300000,
    eventually_const_mul_power_le (by norm_num : (13 : ℝ) < 14) 2] with A hA hbig htwo
  intro μ b V hμ hb hbA hV hq C
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  have hq0 : 0 < 1-μ*b := by linarith only [hq]
  have hη : 0 < workingGateFraction A := Real.rpow_pos_of_pos hA0 _
  have hη1 : workingGateFraction A ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hA (by norm_num)
  have hηlower : 1/A ≤ workingGateFraction A := by
    have hh : A^(-(1 : ℝ)) ≤ A^(-(67 : ℝ)/500) := Real.rpow_le_rpow_of_exponent_le hA (by norm_num)
    simpa only [workingGateFraction,Real.rpow_neg_one,one_div] using hh
  have hM1 : 1 ≤ A^(10 : ℝ) := Real.one_le_rpow hA (by norm_num)
  have hM0 := (Real.rpow_pos_of_pos hA0 (10 : ℝ)).le
  have hMV0 := mul_nonneg hM0 hV.le
  have hlo : (1/32 : ℝ)*(1/A) ≤ (1-μ*b)*workingGateFraction A :=
    mul_le_mul hq hηlower (one_div_pos.mpr hA0).le hq0.le
  have hdiv := div_le_div_of_nonneg_left (by positivity : 0 ≤ 16*A^(10 : ℝ)*V)
    (by positivity : 0 < (1/32 : ℝ)*(1/A)) hlo
  have hp101 : A^(10 : ℝ)*A = A^(11 : ℝ) := by
    calc
      _ = A^(10 : ℝ)*A^(1 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hA0]; norm_num
  have hediv : (16*A^(10 : ℝ)*V)/((1/32 : ℝ)*(1/A)) = 512*A^(11 : ℝ)*V := by
    rw [← hp101]
    field_simp [hA0.ne'] <;> ring
  rw [hediv] at hdiv
  have hBH0 : 0 ≤ b*(A^(10 : ℝ)*V) := mul_nonneg (by linarith only [hb]) hMV0
  have hdivH := div_le_div_of_nonneg_left hBH0 (by norm_num : (0 : ℝ) < 1/32) hq
  have hBA := mul_le_mul_of_nonneg_right hbA hMV0
  have hp210 : A^(2 : ℝ)*A^(10 : ℝ) = A^(12 : ℝ) := by rw [← Real.rpow_add hA0]; norm_num
  have heBH : A^(2 : ℝ)*(A^(10 : ℝ)*V) = A^(12 : ℝ)*V := by rw [← hp210]; ring
  rw [heBH] at hBA
  have htermH : (b*(A^(10 : ℝ)*V))/(1-μ*b) ≤ 32*A^(12 : ℝ)*V := by
    have heq : (b*(A^(10 : ℝ)*V))/(1/32 : ℝ) = 32*(b*(A^(10 : ℝ)*V)) := by ring
    rw [heq] at hdivH
    calc
      _ ≤ 32*(b*(A^(10 : ℝ)*V)) := hdivH
      _ ≤ 32*(A^(12 : ℝ)*V) := mul_le_mul_of_nonneg_left hBA (by norm_num)
      _ = _ := by ring
  have hpow11 : A^(11 : ℝ) ≤ A^(12 : ℝ) := Real.rpow_le_rpow_of_exponent_le hA (by norm_num)
  have hpow10 : A^(10 : ℝ) ≤ A^(12 : ℝ) := Real.rpow_le_rpow_of_exponent_le hA (by norm_num)
  have hpow1 : 1 ≤ A^(12 : ℝ) := Real.one_le_rpow hA (by norm_num)
  have hV12 := mul_le_mul_of_nonneg_right hpow1 hV.le
  have hM12 := mul_le_mul_of_nonneg_right hpow10 hV.le
  have hL12 := mul_le_mul_of_nonneg_right hpow11 hV.le
  have hU := C.U_linear_bound hμ (by linarith only [hb]) hq0 hV.le hM1 hMV0 hη hη1
  have hU12 : C.U ≤ 300000*A^(12 : ℝ)*V := by
    linarith only [hU,hdiv,htermH,hV12,hM12,hL12,hV]
  have hU13 : C.U ≤ A^(13 : ℝ)*V := hU12.trans (by nlinarith only [mul_le_mul_of_nonneg_right hbig hV.le])
  have hU14 : C.U ≤ A^(14 : ℝ)*V := hU13.trans (mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le hA (by norm_num : (13 : ℝ) ≤ 14)) hV.le)
  have haU := C.a_le_source hb hq0
  have htwoV := mul_le_mul_of_nonneg_right htwo hV.le
  exact ⟨hU14,by nlinarith only [haU,hU13,htwoV]⟩

namespace ConeConnectorParameters
variable {μ b V M H η K : ℝ} (C : ConeConnectorParameters μ b V M H η)

theorem traceRadius_bound_of_size (hμ : 0 ≤ μ) (hU : C.U ≤ K*V) (ha : 2*C.a ≤ K*V) (h : List ℝ) :
    C.traceRadius h ≤ K*V*Real.exp (inverseCharge μ h)*(1+smallPositiveSum μ h) := by
  have hcoef : (1-μ)*(2*C.a) ≤ 2*C.a := by
    nlinarith only [mul_nonneg hμ C.a_pos.le]
  have hsum := mul_le_mul_of_nonneg_right (hcoef.trans ha) (smallPositiveSum_nonneg μ h)
  have hh : C.U+(1-μ)*(2*C.a)*smallPositiveSum μ h ≤ K*V*(1+smallPositiveSum μ h) := by
    nlinarith only [hU,hsum]
  have he := mul_le_mul_of_nonneg_left hh (Real.exp_pos (inverseCharge μ h)).le
  unfold traceRadius
  nlinarith only [he]

end ConeConnectorParameters
end
end StrongSilver
