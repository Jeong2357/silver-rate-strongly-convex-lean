-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.OrdinaryPhaseParameters
import StrongSilver.InitialPhaseBudget

namespace StrongSilver
open Real
noncomputable section
set_option maxHeartbeats 1000000

theorem OrdinaryPhaseParameters.mu_cap {A μ b T P : ℝ} {h : List ℝ}
    (W : OrdinaryPhaseParameters A μ b T P h) (hA : 0 < A) : μ*A ≤ 1/2 := by
  have hb : 0 < b := (Real.rpow_pos_of_pos hA _).trans_le W.pivot_lower
  have hT : 0 < T := hb.trans W.b_lt_T
  have ha := (div_le_iff₀ hT).mp W.cap_ratio
  have hh := mul_le_mul_of_nonneg_left ha W.mu_positive.le
  nlinarith only [hh,W.curvature]

theorem OrdinaryPhaseParameters.mu_lt_one {A μ b T P : ℝ} {h : List ℝ}
    (W : OrdinaryPhaseParameters A μ b T P h) (hA : 1 ≤ A) : μ < 1 := by
  have hcap := W.mu_cap (zero_lt_one.trans_le hA)
  have hh := mul_le_mul_of_nonneg_left hA W.mu_positive.le
  nlinarith only [hh,hcap]

theorem InitialPhaseBudget.mu_lt_one {A μ b T κ B : ℝ} {h : List ℝ}
    (W : InitialPhaseBudget A μ b T κ B h) (hA : 1 ≤ A) : μ < 1 := by
  have hT := W.time_positive
  have ha := (div_le_iff₀ hT).mp W.cap_ratio
  have hT1 : 1 ≤ T := by linarith only [ha,hA]
  have hh := mul_le_mul_of_nonneg_left hT1 W.mu_positive.le
  nlinarith only [hh,W.curvature]

end
end StrongSilver
