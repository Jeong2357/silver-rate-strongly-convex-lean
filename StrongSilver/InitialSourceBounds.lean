-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.InitialPhaseScalar

namespace StrongSilver
open Real
noncomputable section

def initialSourceSlopeConstant : ℝ := 2*initialPlaneConstant+initialPlaneConstant*initialScalarSlopeConstant
def initialSourceNormConstant : ℝ := 2*initialPlaneConstant^2+initialQuadraticConstant^2

theorem initialSourceSlopeConstant_positive : 0 < initialSourceSlopeConstant := by
  have := initialPlaneConstant_positive
  have := initialScalarSlopeConstant_positive
  unfold initialSourceSlopeConstant
  positivity
theorem initialSourceNormConstant_positive : 0 < initialSourceNormConstant := by
  have := initialPlaneConstant_positive
  unfold initialSourceNormConstant
  positivity

namespace InitialPhaseBudget
variable {A μ b T κ B e : ℝ} {h : List ℝ} (W : InitialPhaseBudget A μ b T κ B h)
    (L : LocalPhaseCertificate A μ b T e h)
include W L
set_option maxHeartbeats 1800000

theorem kappa_square_bound (heκ : κ ≤ e) : κ^2 ≤ (κ/B)^2*e^2 := by
  have hK := W.ratio_ge_one
  have hK0 : 0 ≤ κ/B := zero_le_one.trans hK
  have hsqK : 1 ≤ (κ/B)^2 := by nlinarith only [hK]
  have he : κ^2 ≤ e^2 := (sq_le_sq₀ W.kappa_positive.le L.e_positive.le).mpr heκ
  have hh := mul_le_mul_of_nonneg_right hsqK (sq_nonneg e)
  nlinarith only [he,hh]

theorem source_slope_cap (heκ : κ ≤ e) :
    L.sourceSlopeCap ≤ initialSourceSlopeConstant*(κ/B)^2*e^2/κ := by
  have hepos := L.e_positive
  let K := κ/B
  have hK : 0 < K := div_pos W.kappa_positive W.B_positive
  have hCp := initialPlaneConstant_positive
  have hCg := initialScalarSlopeConstant_positive
  have hr0 : planarRadius A 0 ≤ 2 := by linarith [L.planar.head_radius_bound,L.planar.scale_le]
  have hplane := mul_le_mul hr0 (W.plane_start L) (norm_nonneg L.R) (by norm_num : (0 : ℝ) ≤ 2)
  have hscalar := mul_le_mul (W.scalar_start_upper L) (W.scalar_slope_cap L) L.scalarSlopeCap_positive.le
    (by positivity : 0 ≤ initialPlaneConstant*(κ/B)*e)
  have hplaneκ := mul_le_mul_of_nonneg_right hplane W.kappa_positive.le
  have hscalarκ := mul_le_mul_of_nonneg_right hscalar W.kappa_positive.le
  have heq : ((initialPlaneConstant*(κ/B)*e)*(initialScalarSlopeConstant*(κ/B)*e/κ))*κ =
      initialPlaneConstant*initialScalarSlopeConstant*(κ/B)^2*e^2 := by field_simp [W.kappa_positive.ne'] <;> ring
  rw [heq] at hscalarκ
  have hκ2 := W.kappa_square_bound L heκ
  have hκscaled := mul_le_mul_of_nonneg_left hκ2 (by positivity : 0 ≤ 2*initialPlaneConstant)
  apply (le_div_iff₀ W.kappa_positive).mpr
  unfold LocalPhaseCertificate.sourceSlopeCap initialSourceSlopeConstant
  nlinarith only [hplaneκ,hscalarκ,hκscaled]

theorem source_norm_squared (heκ : κ ≤ e) :
    ‖L.path.x 0‖^2 ≤ initialSourceNormConstant*(κ/B)^2*e^2 := by
  have hepos := L.e_positive
  have hK : 0 ≤ κ/B := (div_pos W.kappa_positive W.B_positive).le
  have hCp := initialPlaneConstant_positive
  have hCd := initialQuadraticConstant_positive
  have hR := (sq_le_sq₀ (norm_nonneg L.R) (mul_nonneg hCp.le W.kappa_positive.le)).mpr (W.plane_start L)
  have hD := (sq_le_sq₀ L.D_nonnegative (mul_nonneg hCd.le W.kappa_positive.le)).mpr (W.quadratic_pad L)
  have hscalar := (sq_le_sq₀ L.scalar_start_positive.le (by positivity : 0 ≤ initialPlaneConstant*(κ/B)*e)).mpr
    (W.scalar_start_upper L)
  rw [mul_pow] at hR hD
  simp only [mul_pow] at hscalar
  have hκ2 := W.kappa_square_bound L heκ
  have hκR := mul_le_mul_of_nonneg_left hκ2 (sq_nonneg initialPlaneConstant)
  have hκD := mul_le_mul_of_nonneg_left hκ2 (sq_nonneg initialQuadraticConstant)
  rw [L.start,phase_norm_sq]
  unfold initialSourceNormConstant
  nlinarith only [hR,hD,hscalar,hκR,hκD]

end InitialPhaseBudget
end
end StrongSilver
