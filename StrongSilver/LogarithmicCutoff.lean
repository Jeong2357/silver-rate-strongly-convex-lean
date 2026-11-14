-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.HeightCutSelectors

namespace StrongSilver
open Real
noncomputable section
set_option maxHeartbeats 2800000

/-- Inverse of the logarithmic branch at transformed height y. -/
def logarithmicCutoff (μ P y : ℝ) : ℝ := (1-Real.exp (-μ*(P+Real.exp y)))/μ

theorem logarithmicCutoff_factor {μ P y : ℝ} (hμ : 0 < μ) :
    1-μ*logarithmicCutoff μ P y = Real.exp (-μ*(P+Real.exp y)) := by
  unfold logarithmicCutoff
  field_simp <;> ring

theorem logarithmicCutoff_small {μ P y : ℝ} (hμ : 0 < μ) : μ*logarithmicCutoff μ P y < 1 := by
  have hh := logarithmicCutoff_factor (P := P) (y := y) hμ
  have hp := Real.exp_pos (-μ*(P+Real.exp y))
  linarith only [hh,hp]

theorem logarithmicCutoff_positive {μ P y : ℝ} (hμ : 0 < μ) (hP : 0 ≤ P) : 0 < logarithmicCutoff μ P y := by
  apply div_pos _ hμ
  apply sub_pos.mpr
  apply Real.exp_lt_one_iff.mpr
  have hp : 0 < P+Real.exp y := add_pos_of_nonneg_of_pos hP (Real.exp_pos _)
  nlinarith only [hμ,hp]

@[simp] theorem logarithmicStep_cutoff {μ P y : ℝ} (hμ : 0 < μ) :
    logarithmicStep μ (logarithmicCutoff μ P y) = P+Real.exp y := by
  rw [logarithmicStep,logarithmicCutoff_factor hμ,Real.log_exp]
  field_simp <;> ring

theorem logarithmicCutoff_le_branch {μ B P y : ℝ} (hμ : 0 < μ) (hB : μ*B < 1)
    (hheight : P+Real.exp y ≤ logarithmicStep μ B) : logarithmicCutoff μ P y ≤ B := by
  by_contra hn
  have hlt := logarithmicStep_strictMonoOn hμ hB (logarithmicCutoff_small hμ) (lt_of_not_ge hn)
  rw [logarithmicStep_cutoff hμ] at hlt
  exact (not_lt_of_ge hheight) hlt

theorem cappedStep_cutoff {μ B P y : ℝ} (hμ : 0 < μ) (hB : μ*B < 1)
    (hheight : P+Real.exp y ≤ logarithmicStep μ B) :
    cappedStep μ B (logarithmicCutoff μ P y) = P+Real.exp y := by
  rw [cappedStep,if_pos (logarithmicCutoff_le_branch hμ hB hheight),logarithmicStep_cutoff hμ]

/-- Uniform comparison of actual and transformed cutoff sizes. -/
theorem logarithmicCutoff_size {μ P y : ℝ} (hμ : 0 < μ) (hP : 0 ≤ P)
    (hsmall : μ*(P+Real.exp y) ≤ 1/2) :
    (P+Real.exp y)/2 ≤ logarithmicCutoff μ P y ∧ logarithmicCutoff μ P y ≤ P+Real.exp y ∧
      P+Real.exp y-logarithmicCutoff μ P y ≤ 2*μ*(P+Real.exp y)^2 := by
  let A := logarithmicCutoff μ P y
  have hA : 0 < A := logarithmicCutoff_positive hμ hP
  have hupper : A ≤ P+Real.exp y := by
    simpa only [logarithmicStep_cutoff hμ] using logarithmicStep_ge hμ (logarithmicCutoff_small (P := P) (y := y) hμ)
  have hμA : μ*A ≤ 1/2 := (mul_le_mul_of_nonneg_left hupper hμ.le).trans hsmall
  have hdef := logarithmicStep_defect hμ hμA
  rw [logarithmicStep_cutoff hμ] at hdef
  have hquad : 2*μ*A^2 ≤ A := by nlinarith only [hμA,hA]
  have hA2 : A^2 ≤ (P+Real.exp y)^2 := by
    exact pow_le_pow_left₀ hA.le hupper 2
  have hlast := mul_le_mul_of_nonneg_left hA2 (show 0 ≤ 2*μ by positivity)
  exact ⟨by linarith only [hdef,hquad],hupper,hdef.trans hlast⟩

end
end StrongSilver
