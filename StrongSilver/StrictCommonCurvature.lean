-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CommonCurvatureBounds

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 1800000

def strictLargeSteps (κ : ℝ) (h : List ℝ) : List ℝ := h.filter fun b => decide (κ/2 < b)

theorem largeInverseCharge_filter_strict (κ : ℝ) (h : List ℝ) (μ : ℝ) :
    largeInverseCharge κ (strictLargeSteps κ h) μ = largeInverseCharge κ h μ := by
  induction h with
  | nil => rfl
  | cons b h ih =>
    by_cases hb : κ/2 < b <;> simp [strictLargeSteps,largeInverseCharge,List.filter_cons,hb] at ih ⊢ <;> exact ih

theorem strictLargeSteps_count (κ : ℝ) (h : List ℝ) :
    countAbove (strictLargeSteps κ h) (κ/2) = (strictLargeSteps κ h).length := by
  unfold countAbove
  congr 1
  apply List.filter_eq_self.mpr
  intro b hb
  have hh : κ/2 < b := of_decide_eq_true (List.mem_filter.mp hb).2
  simpa only [decide_eq_true_eq] using hh.le

/-- The root-avoidance charge counts only steps strictly above kappa/2.
Steps equal to kappa/2 are uniformly noncritical on the entire interval. -/
theorem exists_common_curvature_strict {κ : ℝ} (hκ : 0 < κ) (h : List ℝ) :
    ∃ μ : ℝ, 1/κ ≤ μ ∧ μ ≤ 9/(8*κ) ∧ (∀ b ∈ h, 1-μ*b ≠ 0) ∧
      largeInverseCharge κ h μ ≤ 32*((strictLargeSteps κ h).length : ℝ) := by
  obtain ⟨μ,hμ,hμu,hcritical,hcharge⟩ := exists_common_curvature hκ (strictLargeSteps κ h)
  have hμ0 : 0 ≤ μ := (one_div_pos.mpr hκ).le.trans hμ
  have hμκ : μ*κ ≤ 9/8 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 8*κ)).mp hμu
    nlinarith only [hh]
  refine ⟨μ,hμ,hμu,?_,?_⟩
  · intro b hb
    by_cases hbLarge : κ/2 < b
    · exact hcritical b (List.mem_filter.mpr ⟨hb,by simpa only [decide_eq_true_eq] using hbLarge⟩)
    · have hmul := mul_le_mul_of_nonneg_left (le_of_not_gt hbLarge) hμ0
      have hh : 0 < 1-μ*b := by nlinarith only [hmul,hμκ]
      exact hh.ne'
  · simpa only [largeInverseCharge_filter_strict,strictLargeSteps_count] using hcharge

end
end StrongSilver
