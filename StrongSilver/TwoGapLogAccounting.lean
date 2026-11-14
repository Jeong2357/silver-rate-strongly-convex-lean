-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.TraceLogPrices

namespace StrongSilver
open Real
noncomputable section
set_option maxHeartbeats 2400000

/-- Exact logarithmic accounting after attaching the ordinary right
gap. The left construction's gain loses precisely twice the ordinary
right-phase logarithmic loss. -/
theorem ordinary_pair_log_identity {A μ br T P F X : ℝ} {hr : List ℝ}
    (W : OrdinaryPhaseParameters A μ br T P hr) (hA : 1 < A) (hF : 0 < F) :
    Real.log F-2*Real.log X =
      Real.log ((ordinaryReferenceFactor A μ br P hr)^2*F)-2*Real.log X-
        2*Real.log ((br-P)/(transformedGapMaximum μ hr+P))+
        2*(1200/Real.log A+μ*transformedGapMaximum μ hr) := by
  have href := W.reference_factor_positive hA
  rw [Real.log_mul (sq_pos_of_pos href).ne' hF.ne',Real.log_pow,W.log_reference_factor hA]
  ring

/-- Passing from a logarithmic improvement to a multiplicative actual
trace factor requires only positivity of the two ordinary references. -/
theorem factor_lower_of_normalized_log {F X Y I : ℝ} (hF : 0 < F) (hX : 0 < X) (hY : 0 < Y)
    (h : I ≤ Real.log F-2*Real.log X-2*Real.log Y) : X^2*Y^2*Real.exp I ≤ F := by
  have hexp := Real.exp_le_exp.mpr (show 2*Real.log X+2*Real.log Y+I ≤ Real.log F by linarith only [h])
  have hXlog : Real.exp (2*Real.log X) = X^2 := by
    rw [show (2:ℝ)*Real.log X = Real.log (X^2) by rw [Real.log_pow]; norm_num]
    exact Real.exp_log (sq_pos_of_pos hX)
  have hYlog : Real.exp (2*Real.log Y) = Y^2 := by
    rw [show (2:ℝ)*Real.log Y = Real.log (Y^2) by rw [Real.log_pow]; norm_num]
    exact Real.exp_log (sq_pos_of_pos hY)
  rw [Real.exp_add,Real.exp_add,hXlog,hYlog,Real.exp_log hF] at hexp
  exact hexp

theorem trace_rate_lower_of_normalized_log {F X Y I r : ℝ} (hr : 0 ≤ r)
    (hF : 0 < F) (hX : 0 < X) (hY : 0 < Y)
    (h : I ≤ Real.log F-2*Real.log X-2*Real.log Y) : r*(X*Y)^2*Real.exp I ≤ r*F := by
  have hp := mul_le_mul_of_nonneg_left (factor_lower_of_normalized_log hF hX hY h) hr
  nlinarith only [hp]

end
end StrongSilver
