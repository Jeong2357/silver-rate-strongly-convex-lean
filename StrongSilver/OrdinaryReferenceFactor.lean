-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PhaseCurvatureBounds
import StrongSilver.OrdinaryPhaseConstruction

namespace StrongSilver
open Real
noncomputable section
set_option maxHeartbeats 1400000

def ordinaryReferenceFactor (A μ b P : ℝ) (h : List ℝ) : ℝ :=
  ((b-P)/(transformedGapMaximum μ h+P))*Real.exp (-(1200/Real.log A+μ*transformedGapMaximum μ h))

namespace OrdinaryPhaseParameters
variable {A μ b T P : ℝ} {h : List ℝ} (W : OrdinaryPhaseParameters A μ b T P h)
include W

theorem small_steps (hA : 0 < A) : ∀ c ∈ h, μ*c < 1 := by
  intro c hc
  by_cases hc0 : 0 < c
  · have hh := (mul_le_mul_of_nonneg_left (W.gap_cap c hc hc0) W.mu_positive.le).trans (W.mu_cap hA)
    linarith only [hh]
  · have hh := mul_nonpos_of_nonneg_of_nonpos W.mu_positive.le (le_of_not_gt hc0)
    linarith only [hh]

theorem pad_lt_pivot (hA : 1 < A) : P < b :=
  W.pad_upper.trans_lt ((Real.rpow_lt_rpow_of_exponent_lt hA (by norm_num : (199 : ℝ)/200 < 499/500)).trans_le W.pivot_lower)

theorem reference_factor_positive (hA : 1 < A) : 0 < ordinaryReferenceFactor A μ b P h := by
  have hA0 : 0 < A := zero_lt_one.trans hA
  have hP : 0 < P := (Real.rpow_pos_of_pos hA0 _).trans_le W.pad_lower
  have hm := transformedGapMaximum_nonnegative W.mu_positive h (W.small_steps hA0)
  unfold ordinaryReferenceFactor
  exact mul_pos (div_pos (sub_pos.mpr (W.pad_lt_pivot hA)) (add_pos_of_nonneg_of_pos hm hP)) (Real.exp_pos _)

end OrdinaryPhaseParameters
end
end StrongSilver
