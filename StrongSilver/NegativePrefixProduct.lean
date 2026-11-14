-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.Transform
import StrongSilver.Scalar.SignedIntervals
import Mathlib.Analysis.Complex.Exponential

namespace StrongSilver
open Scalar.SignedIntervals
noncomputable section
set_option maxHeartbeats 2000000

theorem quadraticMultiplier_le_exp_negative_mass {μ : ℝ} (hμ : 0 ≤ μ)
    (h : List ℝ) (hh : ∀ b ∈ h, μ*b < 1) :
    quadraticMultiplier μ h ≤ Real.exp (μ*negativeMass h) := by
  induction h with
  | nil => simp [negativeMass,quadraticMultiplier]
  | cons b h ih =>
    have htail := fun c hc => hh c (List.mem_cons_of_mem b hc)
    have ht := ih htail
    have hq := (quadraticMultiplier_positive h htail).le
    have hb : 1-μ*b ≤ Real.exp (μ*max (-b) 0) := by
      have hm := mul_le_mul_of_nonneg_left (le_max_left (-b) 0) hμ
      have he := Real.add_one_le_exp (μ*max (-b) 0)
      nlinarith only [hm,he]
    calc
      quadraticMultiplier μ (b::h) = (1-μ*b)*quadraticMultiplier μ h := rfl
      _ ≤ Real.exp (μ*max (-b) 0)*Real.exp (μ*negativeMass h) :=
        mul_le_mul hb ht hq (Real.exp_pos _).le
      _ = Real.exp (μ*negativeMass (b::h)) := by
        rw [← Real.exp_add]
        congr 1
        simp only [negativeMass,List.map_cons,List.sum_cons]
        ring

theorem negativeMass_nonnegative (h : List ℝ) : 0 ≤ negativeMass h := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx
  exact le_max_right _ _

theorem negativeMass_take_le (h : List ℝ) (k : ℕ) : negativeMass (h.take k) ≤ negativeMass h := by
  have he : negativeMass h = negativeMass (h.take k)+negativeMass (h.drop k) := by
    conv_lhs => rw [← List.take_append_drop k h]
    simp only [negativeMass,List.map_append,List.sum_append]
  linarith only [he,negativeMass_nonnegative (h.drop k)]

/-- The positive excess of every product over one is paid only by the
negative steps; positive steps need not be discarded or bounded below. -/
theorem prefix_product_excess_bound {μ : ℝ} (hμ : 0 ≤ μ) (h : List ℝ)
    (hh : ∀ b ∈ h, μ*b < 1) (hsmall : μ*negativeMass h ≤ 1) (k : ℕ) :
    max (quadraticMultiplier μ (h.take k)-1) 0 ≤ 2*μ*negativeMass h := by
  have hn := mul_nonneg hμ (negativeMass_nonnegative h)
  have hq := quadraticMultiplier_le_exp_negative_mass hμ (h.take k)
    (fun b hb => hh b (List.mem_of_mem_take hb))
  have hc := mul_le_mul_of_nonneg_left (negativeMass_take_le h k) hμ
  have hqe := hq.trans (Real.exp_le_exp.mpr hc)
  have he := Real.abs_exp_sub_one_le (x := μ*negativeMass h) (by rw [abs_of_nonneg hn]; exact hsmall)
  have hs := le_abs_self (Real.exp (μ*negativeMass h)-1)
  rw [abs_of_nonneg hn] at he
  apply max_le
  · nlinarith only [hqe,he,hs]
  · nlinarith only [hn]

end
end StrongSilver
