-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.InitialSourceBounds

namespace StrongSilver
open Real
noncomputable section

def initialGateConstant : ℝ := 1/(2*initialHeightConstant*initialSourceSlopeConstant)

theorem initialGateConstant_positive : 0 < initialGateConstant := by
  have := initialHeightConstant_positive
  have := initialSourceSlopeConstant_positive
  unfold initialGateConstant
  positivity

namespace InitialPhaseBudget
variable {A μ b T κ B e : ℝ} {h : List ℝ} (W : InitialPhaseBudget A μ b T κ B h)
    (L : LocalPhaseCertificate A μ b T e h)
include W L
set_option maxHeartbeats 1600000

theorem gate_fraction_lower (heκ : κ ≤ e) :
    initialGateConstant/(κ/B)^2 ≤
      ((((1/T-μ)/32)*Real.exp (-2*negativeLogSum h T)*e^2)/2)/L.sourceSlopeCap := by
  let K := κ/B
  let Ja := ((1/T-μ)/32)*Real.exp (-2*negativeLogSum h T)*e^2
  have hK : 0 < K := div_pos W.kappa_positive W.B_positive
  have hCh := initialHeightConstant_positive
  have hCs := initialSourceSlopeConstant_positive
  have hG := W.source_slope_cap L heκ
  have hJ := W.height_floor_lower L
  have hGκ : L.sourceSlopeCap*κ ≤ initialSourceSlopeConstant*K^2*e^2 := (le_div_iff₀ W.kappa_positive).mp hG
  have hJe : e^2 ≤ Ja*(initialHeightConstant*κ) := (div_le_iff₀ (mul_pos hCh W.kappa_positive)).mp hJ
  have hJscaled := mul_le_mul_of_nonneg_left hJe (mul_nonneg hCs.le (sq_nonneg K))
  have hbound : L.sourceSlopeCap ≤ (initialHeightConstant*initialSourceSlopeConstant*K^2)*Ja := by
    apply (mul_le_mul_iff_right₀ W.kappa_positive).mp
    nlinarith only [hGκ,hJscaled]
  change initialGateConstant/K^2 ≤ (Ja/2)/L.sourceSlopeCap
  rw [initialGateConstant,div_div]
  apply (div_le_div_iff₀ (by positivity : 0 < 2*initialHeightConstant*initialSourceSlopeConstant*K^2) L.sourceSlopeCap_positive).mpr
  nlinarith only [hbound]

end InitialPhaseBudget
end
end StrongSilver
