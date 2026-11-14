-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.LogCutoffLipschitz

namespace StrongSilver
open Real
noncomputable section
set_option maxHeartbeats 4000000

theorem logarithmicCutoff_monotone {μ P : ℝ} (hμ : 0 < μ) : Monotone (logarithmicCutoff μ P) := by
  intro x y hxy
  have hAdd : P+Real.exp x ≤ P+Real.exp y := by linarith only [Real.exp_le_exp.mpr hxy]
  have hh := mul_le_mul_of_nonpos_left hAdd (neg_nonpos.mpr hμ.le)
  have he := Real.exp_le_exp.mpr hh
  exact div_le_div_of_nonneg_right (sub_le_sub_left he 1) hμ.le

theorem logCutoff_monotone {μ P : ℝ} (hμ : 0 < μ) (hP : 0 ≤ P) : Monotone (fun y => Real.log (logarithmicCutoff μ P y)) := by
  intro x y hxy
  exact Real.log_le_log (logarithmicCutoff_positive hμ hP) (logarithmicCutoff_monotone hμ hxy)

/-- Exact inverse at an actual original positive transformed pivot. -/
theorem logarithmicCutoff_inverts {μ P b : ℝ} (hμ : 0 < μ) (hSmall : μ*b < 1)
    (hRoot : P < logarithmicStep μ b) :
    logarithmicCutoff μ P (Real.log (logarithmicStep μ b-P)) = b := by
  unfold logarithmicCutoff
  rw [Real.exp_log (sub_pos.mpr hRoot)]
  have hArg : -μ*(P+(logarithmicStep μ b-P)) = Real.log (1-μ*b) := by
    unfold logarithmicStep
    field_simp [hμ.ne'] <;> ring
  rw [hArg,Real.exp_log (sub_pos.mpr hSmall)]
  field_simp [hμ.ne'] <;> ring

end
end StrongSilver
