-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CommonCurvature

namespace StrongSilver
open Set
noncomputable section

def inverseChargeAbove (s : ℝ) (h : List ℝ) (μ : ℝ) : ℝ :=
  (h.map (fun b => if s ≤ b then inverseLogKernel (1-μ*b) else 0)).sum

theorem inverseLogKernel_le_two {x : ℝ} (hx : 7/16 ≤ x) : inverseLogKernel x ≤ 2 := by
  have hpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hl := Real.one_sub_inv_le_log_of_pos hpos
  have hi : x⁻¹ ≤ 16/7 := by
    have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 7/16) hx
    norm_num [one_div] at hh
    exact hh
  rw [inverseLogKernel_eq]
  exact max_le (by norm_num) (by linarith)

theorem common_curvature_mid_charge {κ μ b : ℝ} (hκ : 0 < κ) (hμ : 0 ≤ μ)
    (hμu : μ ≤ 9/(8*κ)) (hb : κ/4 ≤ b) (hbu : b ≤ κ/2) :
    inverseLogKernel (1-μ*b) ≤ 2 := by
  have hb0 : 0 ≤ b := (by positivity : 0 ≤ κ/4).trans hb
  have hmul := mul_le_mul hμu hbu hb0 (by positivity : 0 ≤ 9/(8*κ))
  have he : (9/(8*κ))*(κ/2) = 9/16 := by field_simp; ring
  rw [he] at hmul
  exact inverseLogKernel_le_two (by linarith)

theorem inverseChargeAbove_quarter_bound {κ μ : ℝ} (hκ : 0 < κ) (hμ : 0 ≤ μ)
    (hμu : μ ≤ 9/(8*κ)) (h : List ℝ) :
    inverseChargeAbove (κ/4) h μ ≤ largeInverseCharge κ h μ+2*(countAbove h (κ/4) : ℝ) := by
  induction h with
  | nil => simp [inverseChargeAbove,largeInverseCharge]
  | cons b h ih =>
    have hstep : (if κ/4 ≤ b then inverseLogKernel (1-μ*b) else 0) ≤
        (if κ/2 < b then inverseLogKernel (1-μ*b) else 0)+2*(if κ/4 ≤ b then 1 else 0) := by
      by_cases hb : κ/4 ≤ b
      · by_cases hlarge : κ/2 < b
        · simp only [hb,hlarge,if_true,mul_one]
          linarith
        · simp only [hb,hlarge,if_true,if_false,zero_add,mul_one]
          exact common_curvature_mid_charge hκ hμ hμu hb (le_of_not_gt hlarge)
      · simp only [hb,if_false,mul_zero,add_zero]
        split_ifs
        · exact inverseLogKernel_nonneg _
        · exact le_rfl
    simp only [inverseChargeAbove,largeInverseCharge,List.map_cons,List.sum_cons] at ih ⊢
    rw [countAbove_cons,Nat.cast_add]
    by_cases hb : κ/4 ≤ b <;> simp only [hb,if_true,if_false,Nat.cast_one,Nat.cast_zero] at hstep ⊢ <;> linarith

theorem exists_common_curvature_with_quarter_bound {κ : ℝ} (hκ : 0 < κ) (h : List ℝ) :
    ∃ μ : ℝ, 1/κ ≤ μ ∧ μ ≤ 9/(8*κ) ∧ (∀ b ∈ h, 1-μ*b ≠ 0) ∧
      largeInverseCharge κ h μ ≤ 32*(countAbove h (κ/2) : ℝ) ∧
      inverseChargeAbove (κ/4) h μ ≤ 34*(countAbove h (κ/4) : ℝ) := by
  obtain ⟨μ,hμ,hμu,hn,hcharge⟩ := exists_common_curvature hκ h
  have hμ0 : 0 ≤ μ := (by positivity : 0 ≤ 1/κ).trans hμ
  have hquarter := inverseChargeAbove_quarter_bound hκ hμ0 hμu h
  have hcount : (countAbove h (κ/2) : ℝ) ≤ (countAbove h (κ/4) : ℝ) := by
    exact_mod_cast countAbove_antitone h (show κ/4 ≤ κ/2 by linarith)
  exact ⟨μ,hμ,hμu,hn,hcharge,by linarith⟩

end
end StrongSilver
