-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.Transform
import StrongSilver.NegativePrefixProduct

namespace StrongSilver
open Scalar.SignedIntervals
noncomputable section
set_option maxHeartbeats 2400000

def absoluteMass (h : List ℝ) : ℝ := (h.map abs).sum

theorem absoluteMass_nonnegative (h : List ℝ) : 0 ≤ absoluteMass h := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx
  exact abs_nonneg b

theorem negativeMass_le_absoluteMass (h : List ℝ) : negativeMass h ≤ absoluteMass h := by
  induction h with
  | nil => exact le_rfl
  | cons b h ih =>
    have hb : max (-b) 0 ≤ |b| := max_le (neg_le_abs b) (abs_nonneg b)
    simpa only [negativeMass,absoluteMass,List.map_cons,List.sum_cons] using add_le_add hb ih

theorem absoluteMass_append (h k : List ℝ) : absoluteMass (h++k) = absoluteMass h+absoluteMass k := by
  simp only [absoluteMass,List.map_append,List.sum_append]

theorem absoluteMass_take_le (h : List ℝ) (k : ℕ) : absoluteMass (h.take k) ≤ absoluteMass h := by
  have hh := absoluteMass_append (h.take k) (h.drop k)
  rw [List.take_append_drop] at hh
  linarith only [hh,absoluteMass_nonnegative (h.drop k)]

/-- A signed-product Bernoulli bound under the total absolute-step budget. -/
theorem small_absolute_mass_product_lower {μ : ℝ} (hμ : 0 ≤ μ) (h : List ℝ)
    (hsmall : μ*absoluteMass h ≤ 1/2) : 1-μ*absoluteMass h ≤ quadraticMultiplier μ h := by
  induction h with
  | nil => simp [absoluteMass,quadraticMultiplier]
  | cons b h ih =>
    have hs : absoluteMass (b::h) = |b|+absoluteMass h := rfl
    rw [hs] at hsmall ⊢
    have hμb := mul_nonneg hμ (abs_nonneg b)
    have hμtail := mul_nonneg hμ (absoluteMass_nonnegative h)
    have htail : μ*absoluteMass h ≤ 1/2 := by nlinarith only [hsmall,hμb]
    have hhead : μ*|b| ≤ 1/2 := by nlinarith only [hsmall,hμtail]
    have ht := ih htail
    have hfactor : 1-μ*|b| ≤ 1-μ*b := by
      have hh := mul_le_mul_of_nonneg_left (le_abs_self b) hμ
      linarith only [hh]
    have h0 : 0 ≤ 1-μ*absoluteMass h := by linarith only [htail]
    have hb0 : 0 ≤ 1-μ*b := by linarith only [hfactor,hhead]
    have hm := mul_le_mul hfactor ht h0 hb0
    change 1-μ*(|b|+absoluteMass h) ≤ (1-μ*b)*quadraticMultiplier μ h
    nlinarith only [hm,mul_nonneg hμb hμtail]

theorem small_absolute_mass_steps {μ : ℝ} (hμ : 0 ≤ μ) (h : List ℝ)
    (hsmall : μ*absoluteMass h ≤ 1/2) : ∀ b ∈ h, μ*b < 1 := by
  induction h with
  | nil => simp
  | cons b h ih =>
    have hs : absoluteMass (b::h) = |b|+absoluteMass h := rfl
    rw [hs] at hsmall
    have hμb := mul_nonneg hμ (abs_nonneg b)
    have hμtail := mul_nonneg hμ (absoluteMass_nonnegative h)
    have htail : μ*absoluteMass h ≤ 1/2 := by nlinarith only [hsmall,hμb]
    intro c hc
    rcases List.mem_cons.mp hc with he | he
    · subst c
      have hh := mul_le_mul_of_nonneg_left (le_abs_self b) hμ
      nlinarith only [hh,hsmall,hμtail]
    · exact ih htail c he

theorem small_absolute_mass_product_bounds {μ : ℝ} (hμ : 0 ≤ μ) (h : List ℝ)
    (hsmall : μ*absoluteMass h ≤ 1/4) :
    1/2 ≤ quadraticMultiplier μ h ∧ quadraticMultiplier μ h ≤ 2 := by
  have hhalf : μ*absoluteMass h ≤ 1/2 := by linarith only [hsmall]
  have hlo := small_absolute_mass_product_lower hμ h hhalf
  have hn := mul_nonneg hμ (negativeMass_nonnegative h)
  have hN := mul_le_mul_of_nonneg_left (negativeMass_le_absoluteMass h) hμ
  have hN1 : μ*negativeMass h ≤ 1 := by linarith only [hN,hsmall]
  have hupper := quadraticMultiplier_le_exp_negative_mass hμ h (small_absolute_mass_steps hμ h hhalf)
  have he := Real.abs_exp_sub_one_le (x := μ*negativeMass h) (by rw [abs_of_nonneg hn]; exact hN1)
  rw [abs_of_nonneg hn] at he
  have hle := le_abs_self (Real.exp (μ*negativeMass h)-1)
  constructor <;> nlinarith only [hlo,hsmall,hupper,he,hle,hN]

theorem small_absolute_mass_prefix_bounds {μ : ℝ} (hμ : 0 ≤ μ) (h : List ℝ)
    (hsmall : μ*absoluteMass h ≤ 1/4) (k : ℕ) :
    1/2 ≤ quadraticMultiplier μ (h.take k) ∧ quadraticMultiplier μ (h.take k) ≤ 2 :=
  small_absolute_mass_product_bounds hμ _
    ((mul_le_mul_of_nonneg_left (absoluteMass_take_le h k) hμ).trans hsmall)

end
end StrongSilver
