-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CutPowerCrudeUpper
import StrongSilver.IndexedNodeDistinctness
import StrongSilver.BandNodeWeightBudget

namespace StrongSilver
open Real ScheduleTree
noncomputable section
set_option maxHeartbeats 4200000

theorem cappedStep_positive_upper_global {μ B : ℝ} (hμ : 0 < μ) (hB : 0 < B) (hcap : μ*B ≤ 1/2) (b : ℝ) :
    max (cappedStep μ B b) 0 ≤ 2*max b 0 := by
  by_cases hb : b ≤ B
  · exact cappedStep_positive_upper hμ hB hcap hb
  · have hBb : B ≤ b := (lt_of_not_ge hb).le
    have hb0 := hB.trans_le hBb
    have hd := (cappedStep_defect (b := b) hμ hcap).2
    rw [min_eq_right hBb] at hd
    have hm := mul_le_mul_of_nonneg_right hcap hB.le
    rw [max_eq_left hb0.le]
    apply max_le
    · nlinarith only [hd,hm,hBb]
    · linarith only [hb0]

def heightStripWeight (φ : ℝ → ℝ) (P a width b : ℝ) : ℝ :=
  if P < φ b ∧ a ≤ Real.log (φ b-P) ∧ Real.log (φ b-P) ≤ a+width then
    Real.exp (nu*Real.log (φ b-P)) else 0

theorem heightStripWeight_nonnegative (φ : ℝ → ℝ) (P a width b : ℝ) : 0 ≤ heightStripWeight φ P a width b := by
  unfold heightStripWeight
  split_ifs
  · exact (Real.exp_pos _).le
  · exact le_rfl

private theorem weight_sum_le_count (f : ℝ → ℝ) (A M : ℝ) (h : List ℝ)
    (hf : ∀ b ∈ h, f b ≤ if A ≤ b then M else 0) : (h.map f).sum ≤ M*(countAbove h A:ℝ) := by
  induction h with
  | nil => simp
  | cons b h ih =>
    have hh := hf b (by simp)
    have hi := ih (fun x hx => hf x (List.mem_cons_of_mem b hx))
    rw [List.map_cons,List.sum_cons,countAbove_cons,Nat.cast_add]
    by_cases hb : A ≤ b
    · simp only [hb,↓reduceIte,Nat.cast_one] at hh ⊢
      linear_combination hh+hi
    · simp only [hb,↓reduceIte,Nat.cast_zero,zero_add] at hh ⊢
      linear_combination hh+hi

theorem height_strip_word_rank {μ B P a width cap : ℝ} (hμ : 0 < μ) (hB : 0 < B) (hcap : μ*B ≤ 1/2)
    (hP : 0 < P) (hA : Real.exp a/2 ≤ cap) (h : List ℝ) :
    (h.map (heightStripWeight (cappedStep μ B) P a width)).sum ≤ 2*weightedCount h cap*Real.exp (nu*width) := by
  let A := Real.exp a/2
  let M := Real.exp (nu*(a+width))
  have hA0 : 0 < A := by dsimp only [A]; positivity
  have hM : 0 ≤ M := (Real.exp_pos _).le
  have hφ0 : cappedStep μ B 0 = 0 := by simp only [cappedStep,if_pos hB.le,logarithmicStep_zero]
  have hφ := cappedStep_strictMono hμ (by linarith only [hcap] : μ*B < 1)
  have hpoint : ∀ b ∈ h, heightStripWeight (cappedStep μ B) P a width b ≤ if A ≤ b then M else 0 := by
    intro b hb
    unfold heightStripWeight
    split
    · rename_i hs
      have hb0 : 0 < b := hφ.lt_iff_lt.mp (by rw [hφ0]; exact hP.trans hs.1)
      have hupper := cappedStep_positive_upper_global hμ hB hcap b
      rw [max_eq_left hb0.le] at hupper
      have he := Real.exp_le_exp.mpr hs.2.1
      rw [Real.exp_log (sub_pos.mpr hs.1)] at he
      have hAb : A ≤ b := by
        dsimp only [A]
        have hh := (le_max_left (cappedStep μ B b) 0).trans hupper
        nlinarith only [he,hh,hP]
      rw [if_pos hAb]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs.2.2 nu_positive.le)
    · split_ifs
      · exact hM
      · exact le_rfl
  have hsum := weight_sum_le_count (heightStripWeight (cappedStep μ B) P a width) A M h hpoint
  have hRank := threshold_le_weightedCount h hA0 hA
  have htwo : (2:ℝ)^nu ≤ 2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) nu_lt_one.le
  have hExp : Real.exp (nu*a) = (2:ℝ)^nu*A^nu := by
    rw [← Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hA0.le]
    have he : (2:ℝ)*A = Real.exp a := by dsimp only [A]; ring
    rw [he,Real.rpow_def_of_pos (Real.exp_pos a),Real.log_exp,mul_comm]
  have hMUpper : M ≤ 2*Real.exp (nu*width)*A^nu := by
    dsimp only [M]
    rw [mul_add,Real.exp_add,hExp]
    have hh := mul_le_mul_of_nonneg_right htwo (mul_nonneg (Real.rpow_pos_of_pos hA0 nu).le (Real.exp_pos (nu*width)).le)
    linear_combination hh
  have hCount := mul_le_mul_of_nonneg_right hMUpper (Nat.cast_nonneg (countAbove h A): (0:ℝ) ≤ countAbove h A)
  have hFinal := mul_le_mul_of_nonneg_left hRank (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (Real.exp_pos (nu*width)).le)
  linear_combination hsum+hCount+hFinal

end
end StrongSilver
