-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.InitialRaisedNorm
import StrongSilver.InitialConeRadius

namespace StrongSilver
open Real
noncomputable section
set_option maxHeartbeats 1600000

def initialBlockConstant : ℝ := (1+5*initialEntryConstant)*initialConeRadiusConstant

theorem initialBlockConstant_positive : 0 < initialBlockConstant := by
  have := initialEntryConstant_positive
  have := initialConeRadiusConstant_positive
  unfold initialBlockConstant
  positivity

theorem initial_exceptional_norm_bound {κ K N U Z H R : ℝ} (hκ : 0 < κ) (hK : 1 ≤ K)
    (hN : 0 ≤ N) (hU : 0 ≤ U) (hUR : U ≤ R) (hZ : Z ≤ 2*R) (hH : κ*H ≤ 2*R)
    (hNsq : N^2 ≤ initialEntryConstant*K^4*(U^2+U*Z+κ*U*H)) :
    N ≤ (1+5*initialEntryConstant)*K^2*R := by
  have hR : 0 ≤ R := hU.trans hUR
  have hsq := (sq_le_sq₀ hU hR).mpr hUR
  have hUZ := mul_le_mul_of_nonneg_left hZ hU
  have hUH := mul_le_mul_of_nonneg_left hH hU
  have hRUR := mul_le_mul_of_nonneg_right hUR hR
  have hsum : U^2+U*Z+κ*U*H ≤ 5*R^2 := by nlinarith only [hsq,hUZ,hUH,hRUR]
  have hCE := initialEntryConstant_positive
  have h1 := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ initialEntryConstant*K^4)
  have hC : 5*initialEntryConstant ≤ (1+5*initialEntryConstant)^2 := by nlinarith only [hCE]
  have h2 := mul_le_mul_of_nonneg_right hC (by positivity : 0 ≤ K^4*R^2)
  have hfinal : N^2 ≤ ((1+5*initialEntryConstant)*K^2*R)^2 := by nlinarith only [hNsq,h1,h2]
  exact (sq_le_sq₀ hN (by positivity : 0 ≤ (1+5*initialEntryConstant)*K^2*R)).mp hfinal

end
end StrongSilver
