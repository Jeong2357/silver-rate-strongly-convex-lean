-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.SmallStepInverseCharge

namespace StrongSilver
open Real
noncomputable section
set_option maxHeartbeats 1400000

def maxPrefixProduct (μ : ℝ) : List ℝ → ℝ
  | [] => 1
  | a::h => max 1 ((1-μ*a)*maxPrefixProduct μ h)

theorem maxPrefixProduct_ge_one (μ : ℝ) (h : List ℝ) : 1 ≤ maxPrefixProduct μ h := by
  cases h with
  | nil => exact le_rfl
  | cons a h => exact le_max_left _ _

theorem quadraticPrefix_le_maxPrefixProduct {μ : ℝ} (h : List ℝ)
    (hh : ∀ a ∈ h, μ*a < 1) (i : ℕ) : quadraticMultiplier μ (h.take i) ≤ maxPrefixProduct μ h := by
  induction h generalizing i with
  | nil => simp [quadraticMultiplier,maxPrefixProduct]
  | cons a h ih =>
    cases i with
    | zero => simpa only [List.take_zero,quadraticMultiplier,List.map_nil,List.prod_nil] using maxPrefixProduct_ge_one μ (a::h)
    | succ i =>
      rw [List.take_succ_cons]
      change (1-μ*a)*quadraticMultiplier μ (h.take i) ≤ max 1 ((1-μ*a)*maxPrefixProduct μ h)
      exact (mul_le_mul_of_nonneg_left (ih (fun b hb => hh b (List.mem_cons_of_mem a hb)) i)
        (by linarith [hh a List.mem_cons_self])).trans (le_max_right _ _)

theorem maxPrefixProduct_attained {μ : ℝ} (h : List ℝ) (hh : ∀ a ∈ h, μ*a < 1) :
    ∃ i : ℕ, i ≤ h.length ∧ quadraticMultiplier μ (h.take i) = maxPrefixProduct μ h := by
  induction h with
  | nil => exact ⟨0,le_rfl,rfl⟩
  | cons a h ih =>
    obtain ⟨i,hi,he⟩ := ih (fun b hb => hh b (List.mem_cons_of_mem a hb))
    by_cases hsmall : (1-μ*a)*maxPrefixProduct μ h ≤ 1
    · refine ⟨0,by omega,?_⟩
      simp only [List.take_zero,quadraticMultiplier,List.map_nil,List.prod_nil,maxPrefixProduct,max_eq_left hsmall]
    · refine ⟨i+1,by simp only [List.length_cons]; omega,?_⟩
      rw [List.take_succ_cons]
      change (1-μ*a)*quadraticMultiplier μ (h.take i) = max 1 ((1-μ*a)*maxPrefixProduct μ h)
      rw [he,max_eq_right (le_of_not_ge hsmall)]

theorem quadraticMultiplier_lower_exp_charge {μ : ℝ} (h : List ℝ) (hh : ∀ a ∈ h, μ*a < 1) :
    Real.exp (-inverseCharge μ h) ≤ quadraticMultiplier μ h := by
  induction h with
  | nil => simp [inverseCharge,quadraticMultiplier]
  | cons a h ih =>
    have hfactor : 0 < 1-μ*a := by linarith [hh a List.mem_cons_self]
    have hk : -Real.log (1-μ*a) ≤ inverseLogKernel (1-μ*a) := by
      rw [inverseLogKernel_eq]
      exact le_max_right _ _
    have hf : Real.exp (-inverseLogKernel (1-μ*a)) ≤ 1-μ*a := by
      calc
        _ ≤ Real.exp (Real.log (1-μ*a)) := Real.exp_le_exp.mpr (by linarith only [hk])
        _ = _ := Real.exp_log hfactor
    have ht := ih (fun b hb => hh b (List.mem_cons_of_mem a hb))
    have hm := mul_le_mul hf ht (Real.exp_pos _).le hfactor.le
    calc
      Real.exp (-inverseCharge μ (a::h)) = Real.exp (-inverseLogKernel (1-μ*a)+(-inverseCharge μ h)) := by
        congr 1
        change -(inverseLogKernel (1-μ*a)+inverseCharge μ h) = _
        ring
      _ = Real.exp (-inverseLogKernel (1-μ*a))*Real.exp (-inverseCharge μ h) := Real.exp_add _ _
      _ ≤ (1-μ*a)*quadraticMultiplier μ h := hm
      _ = quadraticMultiplier μ (a::h) := rfl

theorem positiveMass_drop_le (h : List ℝ) (i : ℕ) :
    Scalar.SignedIntervals.positiveMass (h.drop i) ≤ Scalar.SignedIntervals.positiveMass h := by
  have hh := Scalar.SignedIntervals.positiveMass_append (h.take i) (h.drop i)
  rw [List.take_append_drop] at hh
  linarith only [hh,Scalar.SignedIntervals.positiveMass_nonneg (h.take i)]

theorem terminal_product_lower {μ A : ℝ} (hμ : 0 ≤ μ) (hcap : μ*A ≤ 1/2) (h : List ℝ)
    (hh : ∀ b ∈ h, 0 < b → b ≤ A) :
    maxPrefixProduct μ h*Real.exp (-2*μ*Scalar.SignedIntervals.positiveMass h) ≤ quadraticMultiplier μ h := by
  have hsmall : ∀ b ∈ h, μ*b < 1 := by
    intro b hb
    by_cases hb0 : 0 < b
    · have hm := (mul_le_mul_of_nonneg_left (hh b hb hb0) hμ).trans hcap
      linarith only [hm]
    · have hm := mul_nonpos_of_nonneg_of_nonpos hμ (le_of_not_gt hb0)
      linarith only [hm]
  obtain ⟨i,hi,he⟩ := maxPrefixProduct_attained h hsmall
  have hc := inverseCharge_small_steps hμ hcap (h.drop i) (fun b hb => hh b (List.mem_of_mem_drop hb))
  have hmass := mul_le_mul_of_nonneg_left (positiveMass_drop_le h i) (by linarith only [hμ] : 0 ≤ 2*μ)
  have hexp : Real.exp (-2*μ*Scalar.SignedIntervals.positiveMass h) ≤ Real.exp (-inverseCharge μ (h.drop i)) :=
    Real.exp_le_exp.mpr (by nlinarith only [hc,hmass])
  have htail := hexp.trans (quadraticMultiplier_lower_exp_charge (h.drop i) (fun b hb => hsmall b (List.mem_of_mem_drop hb)))
  have hprod := mul_le_mul_of_nonneg_left htail (zero_le_one.trans (maxPrefixProduct_ge_one μ h))
  have hfull : quadraticMultiplier μ h = quadraticMultiplier μ (h.take i)*quadraticMultiplier μ (h.drop i) := by
    conv_lhs => rw [← List.take_append_drop i h]
    simp only [quadraticMultiplier,List.map_append,List.prod_append]
  rw [he] at hfull
  exact hprod.trans_eq hfull.symm

end
end StrongSilver
