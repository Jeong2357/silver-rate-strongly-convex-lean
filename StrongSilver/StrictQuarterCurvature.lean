-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.StrictCommonCurvature
import StrongSilver.CommonCurvatureBounds

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 1800000

theorem strictLarge_count_le_quarter {κ : ℝ} (hκ : 0 < κ) (h : List ℝ) :
    (strictLargeSteps κ h).length ≤ countAbove h (κ/4) := by
  induction h with
  | nil => simp [strictLargeSteps]
  | cons b h ih =>
    simp only [strictLargeSteps] at ih
    by_cases hb : κ/2 < b
    · have hq : κ/4 ≤ b := by linarith only [hb,hκ]
      simp only [strictLargeSteps,List.filter_cons,hb,decide_true,↓reduceIte,List.length_cons,countAbove_cons,hq,if_true]
      omega
    · simp only [strictLargeSteps,List.filter_cons,hb,decide_false,Bool.false_eq_true,↓reduceIte,countAbove_cons]
      split_ifs <;> omega

theorem exists_strict_common_curvature_with_quarter_bound {κ : ℝ} (hκ : 0 < κ) (h : List ℝ) :
    ∃ μ : ℝ, 1/κ ≤ μ ∧ μ ≤ 9/(8*κ) ∧ (∀ b ∈ h, 1-μ*b ≠ 0) ∧
      largeInverseCharge κ h μ ≤ 32*((strictLargeSteps κ h).length : ℝ) ∧
      inverseChargeAbove (κ/4) h μ ≤ 34*(countAbove h (κ/4) : ℝ) := by
  obtain ⟨μ,hμ,hμu,hcrit,hcharge⟩ := exists_common_curvature_strict hκ h
  have hμ0 : 0 ≤ μ := (one_div_pos.mpr hκ).le.trans hμ
  have hquarter := inverseChargeAbove_quarter_bound hκ hμ0 hμu h
  have hc : ((strictLargeSteps κ h).length : ℝ) ≤ (countAbove h (κ/4) : ℝ) := by
    exact_mod_cast strictLarge_count_le_quarter hκ h
  exact ⟨μ,hμ,hμu,hcrit,hcharge,by linear_combination hquarter+hcharge+32*hc⟩

end
end StrongSilver
