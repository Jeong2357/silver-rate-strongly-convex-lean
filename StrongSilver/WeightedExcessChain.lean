-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.WeightedTelescoping
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace StrongSilver
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2800000

/-- Summation by parts with both nonzero endpoint weights. -/
theorem weighted_difference_endpoints (w L : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, w (i+1)*(L i-L (i+1))) =
      w 0*L 0-w n*L n-∑ i ∈ Finset.range n, (w i-w (i+1))*L i := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ,Finset.sum_range_succ,ih]; ring

/-- The relative weight drops have a logarithmic total, including
repeated pivot heights. No bound on the number of insertions is used. -/
theorem relative_weight_drop_sum (w : ℕ → ℝ) (n : ℕ)
    (hw : ∀ i ≤ n, 0 < w i) :
    (∑ i ∈ Finset.range n, (w i-w (i+1))/w i) ≤ Real.log (w 0)-Real.log (w n) := by
  have hlocal : ∀ i < n, (w i-w (i+1))/w i ≤ Real.log (w i)-Real.log (w (i+1)) := by
    intro i hi
    have hwi := hw i (by omega)
    have hwin := hw (i+1) (by omega)
    have hother := Real.log_le_sub_one_of_pos (div_pos hwin hwi)
    rw [Real.log_div hwin.ne' hwi.ne'] at hother
    have he : (w i-w (i+1))/w i = 1-w (i+1)/w i := by field_simp <;> ring
    rw [he]
    linarith only [hother]
  have hs := Finset.sum_le_sum (s := Finset.range n) (fun i hi => hlocal i (Finset.mem_range.mp hi))
  simpa only [sum_successive_differences] using hs

/-- Finite version of the total-excess estimate (4.9). The jump
identity is the actual split identity when applied to a cut chain. -/
theorem weighted_excess_chain_bound (P L w E : ℕ → ℝ) (n : ℕ) {c M e : ℝ}
    (hc : 0 ≤ c) (he : 0 ≤ e)
    (hw : ∀ i ≤ n, 0 < w i) (hmono : ∀ i < n, w (i+1) ≤ w i)
    (hlower : ∀ i ≤ n, -e ≤ w i*L i)
    (hupper : w 0*L 0 ≤ M) (hP0 : 0 ≤ P 0) (hPn : P n ≤ M)
    (hjump : ∀ i < n, E i = c*w (i+1)*(L i-L (i+1))-(P i-P (i+1))) :
    (∑ i ∈ Finset.range n, E i) ≤ c*(M+e+e*(Real.log (w 0)-Real.log (w n)))+M := by
  have hterm : ∀ i < n, -(w i-w (i+1))*L i ≤ e*((w i-w (i+1))/w i) := by
    intro i hi
    have hwi := hw i (by omega)
    have hl := hlower i (by omega)
    have hd := sub_nonneg.mpr (hmono i hi)
    have hp := mul_le_mul_of_nonneg_left hl (div_nonneg hd hwi.le)
    have heq : (w i-w (i+1))/w i*(w i*L i) = (w i-w (i+1))*L i := by field_simp <;> ring
    rw [heq] at hp
    nlinarith only [hp]
  have hs := Finset.sum_le_sum (s := Finset.range n) (fun i hi => hterm i (Finset.mem_range.mp hi))
  simp only [neg_mul,Finset.sum_neg_distrib] at hs
  rw [← Finset.mul_sum] at hs
  have hlog := mul_le_mul_of_nonneg_left (relative_weight_drop_sum w n hw) he
  have hparts := weighted_difference_endpoints w L n
  have hbound : (∑ i ∈ Finset.range n, w (i+1)*(L i-L (i+1))) ≤
      M+e+e*(Real.log (w 0)-Real.log (w n)) := by
    have hlast := hlower n le_rfl
    linarith only [hparts,hs,hlog,hupper,hlast]
  have hsum : (∑ i ∈ Finset.range n, E i) =
      c*(∑ i ∈ Finset.range n, w (i+1)*(L i-L (i+1)))-(P 0-P n) := by
    calc
      _ = ∑ i ∈ Finset.range n, (c*w (i+1)*(L i-L (i+1))-(P i-P (i+1))) :=
        Finset.sum_congr rfl (fun i hi => hjump i (Finset.mem_range.mp hi))
      _ = _ := by
        rw [Finset.sum_sub_distrib,sum_successive_differences,Finset.mul_sum]
        apply congrArg₂ (fun a b : ℝ => a-b) _ rfl
        apply Finset.sum_congr rfl
        intro i _
        ring
  rw [hsum]
  have hm := mul_le_mul_of_nonneg_left hbound hc
  linarith only [hm,hP0,hPn]

end
end StrongSilver
