-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.TerminalConeSize
import StrongSilver.ConeLocalTrajectory

namespace StrongSilver
open Real
noncomputable section
set_option maxHeartbeats 1800000

theorem cone_trace_radius_scaled {μ b V M H η κ R : ℝ} (C : ConeConnectorParameters μ b V M H η)
    (hμ : 0 ≤ μ) (hκ : 0 < κ) (hU : C.U ≤ R) (hG : κ*(2*C.a) ≤ R) (I : List ℝ) :
    C.traceRadius I ≤ R*Real.exp (inverseCharge μ I)*(1+smallPositiveSum μ I/κ) := by
  have hcoef : (1-μ)*(2*C.a) ≤ 2*C.a := by nlinarith only [mul_nonneg hμ C.a_pos.le]
  have hGa : 2*C.a ≤ R/κ := (le_div_iff₀ hκ).mpr (by nlinarith only [hG])
  have hsum := mul_le_mul_of_nonneg_right (hcoef.trans hGa) (smallPositiveSum_nonneg μ I)
  have hbound : C.U+(1-μ)*(2*C.a)*smallPositiveSum μ I ≤ R*(1+smallPositiveSum μ I/κ) := by
    have he : (R/κ)*smallPositiveSum μ I = R*(smallPositiveSum μ I/κ) := by ring
    rw [he] at hsum
    nlinarith only [hU,hsum]
  have hh := mul_le_mul_of_nonneg_left hbound (Real.exp_pos (inverseCharge μ I)).le
  unfold ConeConnectorParameters.traceRadius
  nlinarith only [hh]

namespace ConeConnectorParameters
variable {μ b V M : ℝ} (C : ConeConnectorParameters μ b V M 0 1)

theorem terminal_scaled_size {κ K : ℝ} (hμ : 0 ≤ μ) (hb : 2 ≤ b) (hM : 1 ≤ M) (hV : 0 < V)
    (hK : 1 ≤ K) (hκKb : κ ≤ K*b) (hq : 1/32 ≤ 1-μ*b) :
    C.U ≤ 1200000*K*Real.sqrt M*V ∧ κ*(2*C.a) ≤ 1200000*K*Real.sqrt M*V := by
  have hU := C.terminal_U_bound hM hV hq
  have hslope := cone_scaled_slope_bound C hμ hb (zero_le_one.trans hK) hκKb hq
  have hUscale := mul_le_mul_of_nonneg_left hU (by linarith only [hK] : 0 ≤ 4*K)
  have hm := Real.sqrt_pos.mpr (zero_lt_one.trans_le hM)
  have hKscale := mul_le_mul_of_nonneg_right hK (by positivity : 0 ≤ 1200000*Real.sqrt M*V)
  exact ⟨by nlinarith only [hU,hKscale,mul_pos hm hV],by nlinarith only [hslope,hUscale]⟩

end ConeConnectorParameters
end
end StrongSilver
