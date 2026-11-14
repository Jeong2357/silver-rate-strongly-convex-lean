-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.Transform

namespace StrongSilver
noncomputable section

/-- Equation (2.11), with an affine continuation above B. -/
def cappedStep (μ B h : ℝ) : ℝ :=
  if h ≤ B then logarithmicStep μ h else h+logarithmicStep μ B-B

theorem cappedStep_monotone {μ B : ℝ} (hμ : 0 < μ) (hB : μ*B < 1) :
    Monotone (cappedStep μ B) := by
  intro a b hab
  by_cases ha : a ≤ B <;> by_cases hb : b ≤ B
  · simp only [cappedStep,if_pos ha,if_pos hb]
    exact logarithmicStep_monotone hμ hab (lt_of_le_of_lt (mul_le_mul_of_nonneg_left hb hμ.le) hB)
  · simp only [cappedStep,if_pos ha,if_neg hb]
    have hl := logarithmicStep_monotone hμ ha hB
    linarith
  · exact False.elim (ha (hab.trans hb))
  · simp only [cappedStep,if_neg ha,if_neg hb]
    linarith

theorem cappedStep_ge {μ B : ℝ} (hμ : 0 < μ) (hB : μ*B < 1) (h : ℝ) : h ≤ cappedStep μ B h := by
  by_cases hh : h ≤ B
  · rw [cappedStep,if_pos hh]
    exact logarithmicStep_ge hμ (lt_of_le_of_lt (mul_le_mul_of_nonneg_left hh hμ.le) hB)
  · rw [cappedStep,if_neg hh]
    have hl := logarithmicStep_ge hμ hB
    linarith

theorem cappedStep_nonpos {μ B h : ℝ} (hμ : 0 < μ) (hB : 0 ≤ B) (hh : h ≤ 0) :
    cappedStep μ B h ≤ 0 := by
  rw [cappedStep,if_pos (hh.trans hB)]
  exact logarithmicStep_nonpos hμ hh

theorem log_one_sub_defect {t : ℝ} (ht : t ≤ 1/2) : -Real.log (1-t)-t ≤ 2*t^2 := by
  have hp : 0 < 1-t := by linarith
  have hl := Real.one_sub_inv_le_log_of_pos hp
  have hinv : (1-t)⁻¹ ≤ 2 := by
    rw [← one_div]
    exact (div_le_iff₀ hp).mpr (by linarith)
  have hid : (1-t)⁻¹-1-t = t^2*(1-t)⁻¹ := by field_simp [hp.ne']; ring
  calc
    _ ≤ (1-t)⁻¹-1-t := by linarith
    _ = t^2*(1-t)⁻¹ := hid
    _ ≤ 2*t^2 := by nlinarith only [mul_le_mul_of_nonneg_left hinv (sq_nonneg t)]

theorem logarithmicStep_defect {μ b : ℝ} (hμ : 0 < μ) (hb : μ*b ≤ 1/2) :
    logarithmicStep μ b-b ≤ 2*μ*b^2 := by
  have hlog := log_one_sub_defect hb
  apply (mul_le_mul_iff_right₀ hμ).mp
  calc
    μ*(logarithmicStep μ b-b) = -Real.log (1-μ*b)-μ*b := by
      unfold logarithmicStep
      field_simp
    _ ≤ 2*(μ*b)^2 := hlog
    _ = μ*(2*μ*b^2) := by ring

theorem cappedStep_defect {μ B b : ℝ} (hμ : 0 < μ) (hB : μ*B ≤ 1/2) :
    0 ≤ cappedStep μ B b-b ∧ cappedStep μ B b-b ≤ 2*μ*(min b B)^2 := by
  have hB1 : μ*B < 1 := by linarith
  refine ⟨sub_nonneg.mpr (cappedStep_ge hμ hB1 b),?_⟩
  by_cases hb : b ≤ B
  · rw [cappedStep,if_pos hb,min_eq_left hb]
    exact logarithmicStep_defect hμ ((mul_le_mul_of_nonneg_left hb hμ.le).trans hB)
  · rw [cappedStep,if_neg hb,min_eq_right (le_of_not_ge hb)]
    have hh := logarithmicStep_defect hμ hB
    linarith

/-- Pointwise logarithmic conversion used in (2.12). -/
theorem selected_factor_conversion {μ B P b : ℝ} (hμ : 0 < μ) (hB : 0 < B)
    (hμB : μ*B ≤ 1/2) (hP : 0 < P) (hb : 2*P ≤ b) :
    0 ≤ Real.log ((cappedStep μ B b-P)/(b-P)) ∧
      Real.log ((cappedStep μ B b-P)/(b-P)) ≤ 4*μ*(min b B) := by
  have hbpos : 0 < b-P := by linarith
  have hb0 : 0 < b := by linarith
  have hmin : 0 < min b B := lt_min hb0 hB
  obtain ⟨hdev0,hdev⟩ := cappedStep_defect (b := b) hμ hμB
  have hphi : 0 < cappedStep μ B b-P := by linarith
  have hratio : 1 ≤ (cappedStep μ B b-P)/(b-P) := (one_le_div hbpos).mpr (by linarith)
  refine ⟨Real.log_nonneg hratio,?_⟩
  have hl := Real.log_le_sub_one_of_pos (div_pos hphi hbpos)
  have hid : (cappedStep μ B b-P)/(b-P)-1 = (cappedStep μ B b-b)/(b-P) := by
    field_simp [hbpos.ne']; ring
  rw [hid] at hl
  apply hl.trans
  apply (div_le_iff₀ hbpos).mpr
  have hmb : min b B ≤ 2*(b-P) := (min_le_left _ _).trans (by linarith)
  have hh := mul_le_mul_of_nonneg_left hmb (mul_nonneg (by positivity : 0 ≤ 2*μ) hmin.le)
  nlinarith only [hdev,hh]

end
end StrongSilver
