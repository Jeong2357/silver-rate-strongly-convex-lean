-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.Scalar.SignedIntervals
import StrongSilver.Quadratics
import StrongSilver.Constants

namespace StrongSilver
noncomputable section

def logarithmicStep (μ h : ℝ) : ℝ := -Real.log (1-μ*h)/μ

@[simp] theorem logarithmicStep_zero (μ : ℝ) : logarithmicStep μ 0 = 0 := by
  simp [logarithmicStep]

theorem logarithmicStep_ge {μ h : ℝ} (hμ : 0 < μ) (hh : μ*h < 1) : h ≤ logarithmicStep μ h := by
  have hl := Real.log_le_sub_one_of_pos (by linarith : 0 < 1-μ*h)
  apply (le_div_iff₀ hμ).mpr
  linarith

theorem logarithmicStep_nonpos {μ h : ℝ} (hμ : 0 < μ) (hh : h ≤ 0) : logarithmicStep μ h ≤ 0 := by
  have hl : 0 ≤ Real.log (1-μ*h) := Real.log_nonneg (by nlinarith)
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hl) hμ.le

theorem logarithmicStep_pos {μ h : ℝ} (hμ : 0 < μ) (hh : 0 < h) (hh1 : μ*h < 1) :
    0 < logarithmicStep μ h := hh.trans_le (logarithmicStep_ge hμ hh1)

theorem logarithmicStep_monotone {μ a b : ℝ} (hμ : 0 < μ) (hab : a ≤ b) (hb : μ*b < 1) :
    logarithmicStep μ a ≤ logarithmicStep μ b := by
  have hb0 : 0 < 1-μ*b := by linarith
  have hba : 1-μ*b ≤ 1-μ*a := by nlinarith
  have hl := Real.log_le_log hb0 hba
  apply (div_le_div_iff_of_pos_right hμ).mpr
  linarith

theorem quadraticMultiplier_positive {μ : ℝ} (h : List ℝ) (hh : ∀ a ∈ h, μ*a < 1) :
    0 < quadraticMultiplier μ h := by
  apply List.prod_pos
  intro b hb
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
  linarith [hh a ha]

theorem logarithmicSteps_sum {μ : ℝ} (h : List ℝ) (hh : ∀ a ∈ h, μ*a < 1) :
    (h.map (logarithmicStep μ)).sum = -Real.log (quadraticMultiplier μ h)/μ := by
  induction h with
  | nil => simp [quadraticMultiplier]
  | cons a h ih =>
    have ha : μ*a < 1 := hh a (by simp)
    have ht : ∀ b ∈ h, μ*b < 1 := fun b hb => hh b (by simp [hb])
    have hp := quadraticMultiplier_positive h ht
    simp only [List.map_cons,List.sum_cons,quadraticMultiplier,List.prod_cons] at *
    rw [ih ht,Real.log_mul (by linarith : 1-μ*a ≠ 0) hp.ne']
    unfold logarithmicStep
    ring

def minPrefixProduct (μ : ℝ) : List ℝ → ℝ
  | [] => 1
  | a::h => min 1 ((1-μ*a)*minPrefixProduct μ h)

theorem minPrefixProduct_positive {μ : ℝ} (h : List ℝ) (hh : ∀ a ∈ h, μ*a < 1) :
    0 < minPrefixProduct μ h := by
  induction h with
  | nil => exact zero_lt_one
  | cons a h ih =>
    have ha : μ*a < 1 := hh a (by simp)
    exact lt_min zero_lt_one (mul_pos (by linarith) (ih (fun b hb => hh b (by simp [hb]))))

/-- Equation (3.1), including the empty prefix and signed gap steps. -/
theorem transformed_prefix_max {μ : ℝ} (hμ : 0 < μ) (h : List ℝ)
    (hh : ∀ a ∈ h, μ*a < 1) :
    Scalar.SignedIntervals.prefixMax (h.map (logarithmicStep μ)) =
      -Real.log (minPrefixProduct μ h)/μ := by
  induction h with
  | nil => simp [Scalar.SignedIntervals.prefixMax,minPrefixProduct]
  | cons a h ih =>
    have ha : μ*a < 1 := hh a (by simp)
    have ht : ∀ b ∈ h, μ*b < 1 := fun b hb => hh b (by simp [hb])
    have hp := minPrefixProduct_positive h ht
    have hap : 0 < (1-μ*a)*minPrefixProduct μ h := mul_pos (by linarith) hp
    rw [List.map_cons,Scalar.SignedIntervals.prefixMax,ih ht,minPrefixProduct]
    have he : logarithmicStep μ a + -Real.log (minPrefixProduct μ h)/μ =
        -Real.log ((1-μ*a)*minPrefixProduct μ h)/μ := by
      rw [Real.log_mul (by linarith : 1-μ*a ≠ 0) hp.ne']
      unfold logarithmicStep
      ring
    rw [he]
    by_cases hb : 1 ≤ (1-μ*a)*minPrefixProduct μ h
    · rw [min_eq_left hb]
      have hl := Real.log_nonneg hb
      rw [max_eq_left (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hl) hμ.le)]
      simp
    · have hb' := le_of_not_ge hb
      rw [min_eq_right hb']
      have hl := Real.log_nonpos hap.le hb'
      exact max_eq_right (div_nonneg (neg_nonneg.mpr hl) hμ.le)

end
end StrongSilver
