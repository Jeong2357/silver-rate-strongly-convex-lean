-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ConeSizeBounds

namespace StrongSilver
open Real
noncomputable section
set_option maxHeartbeats 2000000

namespace ConeConnectorParameters
variable {μ b V M : ℝ} (C : ConeConnectorParameters μ b V M 0 1)

theorem terminal_gamma_bounds (hM : 1 ≤ M) :
    1/(16*Real.sqrt M) ≤ C.γ ∧ C.γ*M ≤ Real.sqrt M := by
  have hM0 : 0 < M := zero_lt_one.trans_le hM
  have hm : 0 < Real.sqrt M := Real.sqrt_pos.mpr hM0
  have hm1 : 1 ≤ Real.sqrt M := Real.one_le_sqrt.mpr hM
  have hsquare := Real.sq_sqrt hM0.le
  have he : Real.sqrt (1/(16*M)) = 1/(4*Real.sqrt M) := by
    rw [Real.sqrt_div zero_le_one,Real.sqrt_one,Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16)]
    norm_num
  have hγeq : C.γ = min (1/16) (1/(4*Real.sqrt M)) := by rw [C.gamma_eq,he]
  have hfirst : 1/(16*Real.sqrt M) ≤ 1/16 := by
    apply (div_le_iff₀ (by positivity : 0 < 16*Real.sqrt M)).mpr
    nlinarith only [hm1]
  have hsecond : 1/(16*Real.sqrt M) ≤ 1/(4*Real.sqrt M) :=
    (one_div_le_one_div (by positivity : 0 < 16*Real.sqrt M) (by positivity : 0 < 4*Real.sqrt M)).mpr (by linarith only [hm])
  have hupper : C.γ ≤ 1/(4*Real.sqrt M) := by rw [hγeq]; exact min_le_right _ _
  have hh := mul_le_mul_of_nonneg_right hupper hM0.le
  have heq : (1/(4*Real.sqrt M))*M = Real.sqrt M/4 := by
    field_simp [hm.ne']
    nlinarith only [hsquare]
  rw [heq] at hh
  exact ⟨by rw [hγeq]; exact le_min hfirst hsecond,by linarith only [hh,hm]⟩

theorem terminal_U_bound (hM : 1 ≤ M) (hV : 0 < V) (hq : 1/32 ≤ 1-μ*b) :
    C.U ≤ 300000*Real.sqrt M*V := by
  have hM0 : 0 < M := zero_lt_one.trans_le hM
  have hm : 0 < Real.sqrt M := Real.sqrt_pos.mpr hM0
  have hm1 : 1 ≤ Real.sqrt M := Real.one_le_sqrt.mpr hM
  have hq0 : 0 < 1-μ*b := by linarith only [hq]
  have hγ := C.terminal_gamma_bounds hM
  have hlo : (1/32 : ℝ)*(1/(16*Real.sqrt M)) ≤ (1-μ*b)*C.γ :=
    mul_le_mul hq hγ.1 (by positivity : 0 ≤ 1/(16*Real.sqrt M)) hq0.le
  have hdiv := div_le_div_of_nonneg_left hV.le (by positivity : 0 < (1/32 : ℝ)*(1/(16*Real.sqrt M))) hlo
  have he : V/((1/32 : ℝ)*(1/(16*Real.sqrt M))) = 512*Real.sqrt M*V := by
    field_simp [hm.ne'] <;> ring
  rw [he] at hdiv
  have hMγ := mul_le_mul_of_nonneg_right hγ.2 hV.le
  have hVscale := mul_le_mul_of_nonneg_right hm1 hV.le
  have hU := C.U_eq
  simp only [mul_zero,zero_div,add_zero] at hU
  nlinarith only [hU,hdiv,hMγ,hVscale,hV]

end ConeConnectorParameters

theorem cone_scaled_slope_bound {μ b V M H η κ K : ℝ} (C : ConeConnectorParameters μ b V M H η)
    (hμ : 0 ≤ μ) (hb : 2 ≤ b) (hK : 0 ≤ K) (hκKb : κ ≤ K*b) (hq : 1/32 ≤ 1-μ*b) :
    κ*(2*C.a) ≤ 4*K*C.U := by
  have hb0 : 0 < b := by linarith only [hb]
  have hq1 : 1-μ*b ≤ 1 := by have hh := mul_nonneg hμ hb0.le; linarith only [hh]
  have hD : b/2 ≤ (1-μ)*b := by nlinarith only [hq,hb]
  have hDa := mul_le_mul_of_nonneg_right hD C.a_pos.le
  have hqU := mul_le_mul_of_nonneg_right hq1 C.U_pos.le
  have hba : b*C.a ≤ 2*C.U := by nlinarith only [hDa,hqU,C.connector_a]
  have hκa := mul_le_mul_of_nonneg_right hκKb C.a_pos.le
  have hbaK := mul_le_mul_of_nonneg_left hba hK
  nlinarith only [hκa,hbaK]

end
end StrongSilver
