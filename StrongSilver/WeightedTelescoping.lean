-- SPDX-License-Identifier: GPL-3.0-only
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

namespace StrongSilver
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1400000

theorem sum_successive_differences (f : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, (f i-f (i+1))) = f 0-f n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ,ih]; ring

/-- Finite summation by parts, retaining the final weight explicitly. -/
theorem weighted_difference_identity (w L : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, w (i+1)*(L i-L (i+1))) =
      w 0*L 0-w (n+1)*L n-∑ i ∈ Finset.range (n+1), (w i-w (i+1))*L i := by
  induction n with
  | zero => simp; ring
  | succ n ih =>
    rw [Finset.sum_range_succ,ih]
    conv_rhs => rw [Finset.sum_range_succ]
    ring

/-- The split inequalities imply the weighted lower bound (3.34). -/
theorem weighted_split_chain_lower (P L w : ℕ → ℝ) (c : ℝ) (n : ℕ)
    (hstep : ∀ i < n, P i-P (i+1) ≤ c*w (i+1)*(L i-L (i+1))) (hend : w (n+1) = 0) :
    P 0-c*w 0*L 0+c*(∑ i ∈ Finset.range (n+1), (w i-w (i+1))*L i) ≤ P n := by
  have hs := Finset.sum_le_sum (s := Finset.range n) (fun i hi => hstep i (Finset.mem_range.mp hi))
  have he : (∑ i ∈ Finset.range n, c*w (i+1)*(L i-L (i+1))) =
      c*(∑ i ∈ Finset.range n, w (i+1)*(L i-L (i+1))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [sum_successive_differences,he,weighted_difference_identity,hend,zero_mul,sub_zero] at hs
  nlinarith only [hs]

theorem weight_differences_sum (w : ℕ → ℝ) (n : ℕ) (hend : w (n+1) = 0) :
    (∑ i ∈ Finset.range (n+1), (w i-w (i+1))) = w 0 := by
  rw [sum_successive_differences,hend,sub_zero]

/-- One new selected step is inserted at each split. -/
theorem weighted_count_identity (w k : ℕ → ℝ) (n : ℕ)
    (hk : ∀ i < n, k (i+1) = k i+1) (hend : w (n+1) = 0) :
    (∑ i ∈ Finset.range (n+1), (w i-w (i+1))*k i) =
      k 0*w 0+∑ i ∈ Finset.range n, w (i+1) := by
  have hh := weighted_difference_identity w k n
  rw [hend,zero_mul,sub_zero] at hh
  have he : (∑ i ∈ Finset.range n, w (i+1)*(k i-k (i+1))) = -(∑ i ∈ Finset.range n, w (i+1)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hk i (Finset.mem_range.mp hi)]
    ring
  rw [he] at hh
  nlinarith only [hh]

/-- A uniform logarithmic error is charged once, while the selected-count
error is charged by the weighted count identity. -/
theorem weighted_log_lower (w L k : ℕ → ℝ) (E δ : ℝ) (n : ℕ)
    (hw : ∀ i ≤ n, w (i+1) ≤ w i) (hend : w (n+1) = 0)
    (hL : ∀ i ≤ n, -E-δ*k i ≤ L i) :
    -E*w 0-δ*(∑ i ∈ Finset.range (n+1), (w i-w (i+1))*k i) ≤
      ∑ i ∈ Finset.range (n+1), (w i-w (i+1))*L i := by
  have hs := Finset.sum_le_sum (s := Finset.range (n+1)) (fun i hi =>
    mul_le_mul_of_nonneg_left (hL i (by have hh := Finset.mem_range.mp hi; omega))
      (sub_nonneg.mpr (hw i (by have hh := Finset.mem_range.mp hi; omega))))
  have he : (∑ i ∈ Finset.range (n+1), (w i-w (i+1))*(-E-δ*k i)) =
      -E*w 0-δ*(∑ i ∈ Finset.range (n+1), (w i-w (i+1))*k i) := by
    have hterm (i : ℕ) : (w i-w (i+1))*(-E-δ*k i) =
        (-E)*(w i-w (i+1))-δ*((w i-w (i+1))*k i) := by ring
    simp_rw [hterm]
    rw [Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.mul_sum,weight_differences_sum w n hend]
  rwa [he] at hs

end
end StrongSilver
