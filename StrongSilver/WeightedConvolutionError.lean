-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FiniteListIntegral
import StrongSilver.FinitePropFilteredSum
import Mathlib.Tactic

namespace StrongSilver
open Real Set MeasureTheory
noncomputable section
set_option maxHeartbeats 7000000

/-- A finite signed convolution error. The normalization is required
only after multiplication by the original event weight, so events of
zero averaging weight need no containment hypothesis. -/
theorem weighted_convolution_error (kernel χ : ℝ → ℝ) (a b m ε χe Δ : ℝ)
    (hab : a ≤ b) (hm : 0 < m) (hε : 0 ≤ ε)
    (hk : IntervalIntegrable kernel volume a b)
    (hχk : IntervalIntegrable (fun y => χ y*kernel y) volume a b)
    (hk0 : ∀ y ∈ Icc a b, 0 ≤ kernel y)
    (hMass : χe*(∫ y in a..b, kernel y) = χe*m)
    (hUpper : (∫ y in a..b, kernel y) ≤ m)
    (hDiff : ∀ y ∈ Icc a b, kernel y ≠ 0 → |χe-χ y| ≤ ε) :
    |χe*Δ-(Δ/m)*(∫ y in a..b, χ y*kernel y)| ≤ ε*|Δ| := by
  let J := ∫ y in a..b, (χe*kernel y-χ y*kernel y)
  have hJint := (hk.const_mul χe).sub hχk
  have hPoint (y : ℝ) (hy : y ∈ Icc a b) :
      -ε*kernel y ≤ χe*kernel y-χ y*kernel y ∧ χe*kernel y-χ y*kernel y ≤ ε*kernel y := by
    by_cases hz : kernel y = 0
    · simp only [hz,mul_zero,sub_self,le_refl,and_self]
    · have hAbs := abs_le.mp (hDiff y hy hz)
      have hLow := mul_le_mul_of_nonneg_right hAbs.1 (hk0 y hy)
      have hHigh := mul_le_mul_of_nonneg_right hAbs.2 (hk0 y hy)
      constructor
      · linear_combination hLow
      · linear_combination hHigh
  have hLo := intervalIntegral.integral_mono_on hab (hk.const_mul (-ε)) hJint (fun y hy => (hPoint y hy).1)
  have hHi := intervalIntegral.integral_mono_on hab hJint (hk.const_mul ε) (fun y hy => (hPoint y hy).2)
  rw [intervalIntegral.integral_const_mul] at hLo hHi
  have hScale := mul_le_mul_of_nonneg_left hUpper hε
  have hAbsJ : |J| ≤ ε*m := abs_le.mpr ⟨by dsimp only [J]; linarith only [hLo,hScale],by dsimp only [J]; linarith only [hHi,hScale]⟩
  have hJ : J = χe*(∫ y in a..b, kernel y)-(∫ y in a..b, χ y*kernel y) := by
    dsimp only [J]
    rw [intervalIntegral.integral_sub (hk.const_mul χe) hχk,intervalIntegral.integral_const_mul]
  have hIdentity : χe*Δ-(Δ/m)*(∫ y in a..b, χ y*kernel y) = (Δ/m)*J := by
    rw [hJ]
    field_simp [hm.ne']
    linear_combination -Δ*hMass
  rw [hIdentity,abs_mul,abs_div,abs_of_pos hm]
  calc
    _ ≤ (|Δ|/m)*(ε*m) := mul_le_mul_of_nonneg_left hAbsJ (div_nonneg (abs_nonneg Δ) hm.le)
    _ = _ := by field_simp [hm.ne'] <;> ring

/-- Finite summation of signed event errors retains every occurrence. -/
theorem list_abs_sum_sub_le {α : Type*} (f g e : α → ℝ) (xs : List α)
    (h : ∀ x ∈ xs, |f x-g x| ≤ e x) :
    |(xs.map f).sum-(xs.map g).sum| ≤ (xs.map e).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hTail := ih (fun z hz => h z (List.mem_cons_of_mem x hz))
    have hHead := h x List.mem_cons_self
    simp only [List.map_cons,List.sum_cons]
    have hTri := abs_add_le (f x-g x) ((xs.map f).sum-(xs.map g).sum)
    have hEq : f x+(xs.map f).sum-(g x+(xs.map g).sum) = (f x-g x)+((xs.map f).sum-(xs.map g).sum) := by ring
    rw [hEq]
    linear_combination hTri+hHead+hTail

end
end StrongSilver
