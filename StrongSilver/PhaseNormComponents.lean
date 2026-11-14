-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PhaseCoordinates

namespace StrongSilver
open Real
noncomputable section
set_option maxHeartbeats 800000

theorem phase_norm_le_sum (R : ℂ) (D a : ℝ) : ‖phasePoint R D a‖ ≤ ‖R‖+|D|+|a| := by
  have hh := phase_norm_sq R D a
  have hD := sq_abs D
  have ha := sq_abs a
  have h1 := mul_nonneg (norm_nonneg R) (abs_nonneg D)
  have h2 := mul_nonneg (norm_nonneg R) (abs_nonneg a)
  have h3 := mul_nonneg (abs_nonneg D) (abs_nonneg a)
  nlinarith only [hh,hD,ha,h1,h2,h3,norm_nonneg (phasePoint R D a),norm_nonneg R,abs_nonneg D,abs_nonneg a]

theorem phase_scalar_le_norm (R : ℂ) (D a : ℝ) : a ≤ ‖phasePoint R D a‖ := by
  have hh := phase_norm_sq R D a
  nlinarith only [hh,sq_nonneg ‖R‖,sq_nonneg D,norm_nonneg (phasePoint R D a)]

end
end StrongSilver
