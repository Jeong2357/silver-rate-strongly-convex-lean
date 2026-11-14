-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.OrderedFullCutBound
import StrongSilver.InitialCutPowerReserve
import StrongSilver.PowerReservePropagation

namespace StrongSilver
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2200000

theorem weighted_log_shift_identity (w L : ℕ → ℝ) (offset : ℝ) (n : ℕ)
    (hend : w (n+1) = 0) :
    (∑ i ∈ Finset.range (n+1), (w i-w (i+1))*(L i-offset)) =
      (∑ i ∈ Finset.range (n+1), (w i-w (i+1))*L i)-w 0*offset := by
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib,← Finset.sum_mul,weight_differences_sum w n hend]

/-- The weighted split bound is unchanged by a common offset in all logs. -/
theorem weighted_chain_shift {P L w : ℕ → ℝ} {c offset : ℝ} {n : ℕ}
    (hend : w (n+1) = 0)
    (hh : P 0-c*w 0*L 0+c*(∑ i ∈ Finset.range (n+1), (w i-w (i+1))*L i) ≤ P n) :
    P 0-c*w 0*(L 0-offset)+c*(∑ i ∈ Finset.range (n+1), (w i-w (i+1))*(L i-offset)) ≤ P n := by
  rw [weighted_log_shift_identity w L offset n hend]
  nlinarith only [hh]

/-- Initial reserve and actual sorted cut insertions, with logarithmic errors
charged by the exact selected-count identity. -/
theorem ordered_full_cut_power_lower {φ : ℝ → ℝ} (hφ : Monotone φ) (h : List ℝ)
    {A B P reserve E δ : ℝ} (hAB : A < B) (hP : 0 < P) (hφA : P < φ A)
    (hr : 0 < reserve) (hbr : φ B-P ≤ reserve)
    (hL : let ps := orderedPositions h (eligibleIndices h Finset.univ A B)
      ∀ i ≤ ps.length, -E-δ*((countAbove h B : ℝ)+(i : ℝ)) ≤
        cutLogProduct φ P reserve (positionCut (fun _ b => decide (B ≤ b)) h (ps.take i))-Real.log reserve) :
    let ps := orderedPositions h (eligibleIndices h Finset.univ A B)
    let w := eligibleRefinementWeights φ P h Finset.univ A B
    ((countAbove h B : ℝ)+1)*powerLogMinimum*(φ B-P)^nu-
      splitCoefficient*(E*(φ B-P)^nu+δ*((countAbove h B : ℝ)*(φ B-P)^nu+
        ∑ i ∈ Finset.range ps.length, w (i+1))) ≤ cutPower φ P reserve (fullCut A h) := by
  let ps := orderedPositions h (eligibleIndices h Finset.univ A B)
  let w := eligibleRefinementWeights φ P h Finset.univ A B
  let C := fun i => positionCut (fun _ b => decide (B ≤ b)) h (ps.take i)
  let k : ℕ → ℝ := fun i => (countAbove h B : ℝ)+(i : ℝ)
  have hs : C 0 = closedCut B h := by simp only [C,List.take_zero,positionCut_nil_closed]
  have he : C ps.length = fullCut A h := by
    change positionCut (fun _ b => decide (B ≤ b)) h (ps.take ps.length) = fullCut A h
    rw [List.take_length]
    exact ordered_positionCut_final h hAB
  have hw0 : w 0 = (φ B-P)^nu := rfl
  have hend : w (ps.length+1) = 0 := eligibleRefinementWeights_end φ P h Finset.univ A B
  have hraw : cutPower φ P reserve (C 0)-splitCoefficient*w 0*cutLogProduct φ P reserve (C 0)+
      splitCoefficient*(∑ i ∈ Finset.range (ps.length+1), (w i-w (i+1))*cutLogProduct φ P reserve (C i)) ≤
      cutPower φ P reserve (C ps.length) := by
    simpa only [hs,he,w,eligibleRefinementWeights,refinementWeights_zero] using
      ordered_full_cut_weighted_lower φ hφ h hAB hP hφA hr.le
  have hchain := weighted_chain_shift (P := fun i => cutPower φ P reserve (C i))
    (L := fun i => cutLogProduct φ P reserve (C i)) (offset := Real.log reserve) hend hraw
  have hb : P < φ B := hφA.trans_le (hφ hAB.le)
  have hreserve := closed_cut_initial_power_reserve hφ hP hb hr hbr h
  have hreserve' : ((countAbove h B : ℝ)+1)*powerLogMinimum*(φ B-P)^nu ≤
      cutPower φ P reserve (C 0)-splitCoefficient*w 0*(cutLogProduct φ P reserve (C 0)-Real.log reserve) := by
    simpa only [hs,hw0] using hreserve
  have hh := power_reserve_propagation (fun i => cutPower φ P reserve (C i))
    (fun i => cutLogProduct φ P reserve (C i)-Real.log reserve) w k
    split_coefficient_positive.le ps.length
    (fun i _ => eligibleRefinementWeights_decreasing hφ hφA hAB.le h Finset.univ i) hend
    (by intro i _; simp only [k,Nat.cast_add,Nat.cast_one]; ring)
    hL hreserve' hchain
  simpa only [he,k,Nat.cast_zero,add_zero,hw0] using hh

end
end StrongSilver
