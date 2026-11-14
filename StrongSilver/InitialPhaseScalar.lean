-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.InitialPhaseGeometry

namespace StrongSilver
open Real
noncomputable section

def initialScalarStartConstant : ℝ := 2*Real.exp 2
def initialScalarSlopeConstant : ℝ := 4*initialPlaneConstant+2
def initialHeightConstant : ℝ := 1024*Real.exp 4

theorem initialScalarStartConstant_positive : 0 < initialScalarStartConstant := by unfold initialScalarStartConstant; positivity
theorem initialScalarSlopeConstant_positive : 0 < initialScalarSlopeConstant := by
  have := initialPlaneConstant_positive
  unfold initialScalarSlopeConstant
  positivity
theorem initialHeightConstant_positive : 0 < initialHeightConstant := by unfold initialHeightConstant; positivity

namespace InitialPhaseBudget
variable {A μ b T κ B e : ℝ} {h : List ℝ} (W : InitialPhaseBudget A μ b T κ B h)
    (L : LocalPhaseCertificate A μ b T e h)
include W L
set_option maxHeartbeats 1800000

theorem scalar_growth : scalarRampGrowth T A b h ≤ initialPlaneConstant*(κ/B) := by
  have hh := W.growth
  have hK : 0 ≤ κ/B := zero_le_one.trans W.ratio_ge_one
  unfold initialPlaneConstant
  nlinarith only [hh,mul_nonneg (Real.exp_pos 4).le hK]

theorem scalar_start_upper : L.scalar.x ≤ initialPlaneConstant*(κ/B)*e := by
  have hupper := (L.scalar.estimates 0 (by omega)).2.1
  simp only [List.take_zero,iterate_nil] at hupper
  exact hupper.trans (mul_le_mul_of_nonneg_right (W.scalar_growth L) L.e_positive.le)

theorem scalar_start_lower : e/initialScalarStartConstant ≤ L.scalar.x := by
  have hepos := L.e_positive
  have hExp : Real.exp (-2) ≤ Real.exp (-negativeLogSum h T) := Real.exp_le_exp.mpr (by linarith [W.negative_charge])
  have hh := mul_le_mul_of_nonneg_left hExp (by positivity : 0 ≤ e/2)
  have hbase := (L.scalar.estimates 0 (by omega)).1
  simp only [List.take_zero,iterate_nil] at hbase
  have heq : (e/2)*Real.exp (-2) = e/initialScalarStartConstant := by
    unfold initialScalarStartConstant
    rw [Real.exp_neg]
    field_simp [(Real.exp_pos 2).ne'] <;> ring
  rw [heq] at hh
  exact hh.trans hbase

theorem scalar_slope_cap : L.scalarSlopeCap ≤ initialScalarSlopeConstant*(κ/B)*e/κ := by
  let K := κ/B
  have hK : 0 < K := div_pos W.kappa_positive W.B_positive
  have hCK : 0 ≤ initialPlaneConstant*K := mul_nonneg initialPlaneConstant_positive.le hK.le
  have hCT := W.scalar_growth L
  change scalarRampGrowth T A b h ≤ initialPlaneConstant*K at hCT
  have h1 := mul_le_mul_of_nonneg_right hCT W.kappa_positive.le
  have h2 := mul_le_mul_of_nonneg_left (show κ ≤ 2*T by linarith [W.time_lower]) hCK
  have hdiv : scalarRampGrowth T A b h/T ≤ (2*initialPlaneConstant*K)/κ := by
    apply (div_le_div_iff₀ W.time_positive W.kappa_positive).mpr
    nlinarith only [h1,h2]
  have hbinv : 1/b ≤ K/κ := by
    have hh := (one_div_le_one_div W.pivot_positive W.B_positive).mpr W.pivot_lower
    have he : K/κ = 1/B := by dsimp only [K]; field_simp [W.kappa_positive.ne',W.B_positive.ne']
    rwa [← he] at hh
  have hsum := add_le_add hdiv hbinv
  have he0 : 0 ≤ 2*e := by have := L.e_positive; positivity
  have hh := mul_le_mul_of_nonneg_right hsum he0
  change 2*(scalarRampGrowth T A b h/T+1/b)*e ≤ initialScalarSlopeConstant*K*e/κ
  unfold initialScalarSlopeConstant
  calc
    _ = (scalarRampGrowth T A b h/T+1/b)*(2*e) := by ring
    _ ≤ (2*initialPlaneConstant*K/κ+K/κ)*(2*e) := hh
    _ = _ := by ring

theorem height_floor_lower : e^2/(initialHeightConstant*κ) ≤
    ((1/T-μ)/32)*Real.exp (-2*negativeLogSum h T)*e^2 := by
  have hκ := W.kappa_positive
  have hT := W.time_positive
  have hcoef : 1/(1024*T) ≤ (1/T-μ)/32 := by
    apply (div_le_iff₀ (mul_pos (by norm_num) W.time_positive)).mpr
    have he : ((1/T-μ)/32)*(1024*T) = 32*(1-μ*T) := by field_simp [W.time_positive.ne'] <;> ring
    rw [he]
    nlinarith only [W.curvature]
  have hrecip : 1/(1024*κ) ≤ 1/(1024*T) :=
    (one_div_le_one_div (by positivity : 0 < 1024*κ) (by positivity : 0 < 1024*T)).mpr
      (mul_le_mul_of_nonneg_left W.time_upper (by norm_num))
  have hcoef' := hrecip.trans hcoef
  have hExp : Real.exp (-4) ≤ Real.exp (-2*negativeLogSum h T) :=
    Real.exp_le_exp.mpr (by linarith [W.negative_charge])
  have hcoef0 : 0 ≤ (1/T-μ)/32 := (by positivity : 0 ≤ 1/(1024*κ)).trans hcoef'
  have hh := mul_le_mul hcoef' hExp (Real.exp_pos _).le hcoef0
  have hh' := mul_le_mul_of_nonneg_right hh (sq_nonneg e)
  have heq : (1/(1024*κ))*Real.exp (-4)*e^2 = e^2/(initialHeightConstant*κ) := by
    unfold initialHeightConstant
    rw [Real.exp_neg]
    field_simp [W.kappa_positive.ne',(Real.exp_pos 4).ne'] <;> ring
  rwa [heq] at hh'

end InitialPhaseBudget
end
end StrongSilver
