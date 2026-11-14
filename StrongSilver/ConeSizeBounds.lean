-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ConeConnectorParameters

namespace StrongSilver.ConeConnectorParameters
open Real
noncomputable section
variable {μ b V M H η : ℝ} (C : ConeConnectorParameters μ b V M H η)
set_option maxHeartbeats 1400000

theorem gamma_lower_linear (hM : 1 ≤ M) (hη : 0 < η) (hη1 : η ≤ 1) :
    η/(16*M) ≤ C.γ := by
  have hM0 : 0 < M := zero_lt_one.trans_le hM
  have ht0 : 0 ≤ η/(16*M) := div_nonneg hη.le (by positivity)
  have ht16 : η/(16*M) ≤ 1/16 := by
    apply (div_le_iff₀ (by positivity : 0 < 16*M)).mpr
    linarith only [hη1,hM]
  have ht1 : η/(16*M) ≤ 1 := by linarith only [ht16]
  have hsquare := Real.sq_sqrt ht0
  have hroot := Real.sqrt_nonneg (η/(16*M))
  have htroot : η/(16*M) ≤ Real.sqrt (η/(16*M)) := by nlinarith only [hsquare,hroot,ht0,ht1]
  rw [C.gamma_eq]
  exact le_min ht16 htroot

theorem U_linear_bound (hμ : 0 ≤ μ) (hb : 0 ≤ b) (hq : 0 < 1-μ*b) (hV : 0 ≤ V)
    (hM : 1 ≤ M) (hH : 0 ≤ H) (hη : 0 < η) (hη1 : η ≤ 1) :
    C.U ≤ 512*(V+(16*M*V)/((1-μ*b)*η)+M*V+(b*H)/(1-μ*b)) := by
  have hM0 : 0 < M := zero_lt_one.trans_le hM
  have hγ := C.gamma_lower_linear hM hη hη1
  have hγmul := (div_le_iff₀ (by positivity : 0 < 16*M)).mp hγ
  have hqη : 0 < (1-μ*b)*η := mul_pos hq hη
  have hqγ : 0 < (1-μ*b)*C.γ := mul_pos hq C.gamma_pos
  have hdiv : V/((1-μ*b)*C.γ) ≤ (16*M*V)/((1-μ*b)*η) := by
    apply (div_le_div_iff₀ hqγ hqη).mpr
    have hh := mul_le_mul_of_nonneg_left hγmul (mul_nonneg hV hq.le)
    nlinarith only [hh]
  have hγ1 : C.γ ≤ 1 := by linarith [C.gamma_small]
  have hMγ := mul_le_mul_of_nonneg_right hγ1 (mul_nonneg hM0.le hV)
  have hDH : ((1-μ)*b)*H ≤ b*H := by
    have hh := mul_nonneg (mul_nonneg hμ hb) hH
    nlinarith only [hh]
  have hdivH := div_le_div_of_nonneg_right hDH hq.le
  rw [C.U_eq]
  nlinarith only [hdiv,hMγ,hdivH]

theorem a_le_source (hb : 1 ≤ b) (hq : 0 < 1-μ*b) : C.a ≤ C.U := by
  have hDq : 1-μ*b ≤ (1-μ)*b := by nlinarith only [hb]
  have hh := mul_le_mul_of_nonneg_right hDq C.a_pos.le
  nlinarith only [hh,C.connector_a,hq]

end
end StrongSilver.ConeConnectorParameters
