-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ShiftedCutPowerBound

namespace StrongSilver
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2400000

/-- The actual ordered cut chain propagates any proved initial reserve.
A common power offset and a common log offset are allowed, which removes
the artificial terminal factor in a compressed tracked schedule. -/
theorem ordered_cut_power_from_reserve {φ : ℝ → ℝ} (hφ : Monotone φ) (h : List ℝ)
    {A B P reserve E δ H powerOffset logOffset : ℝ} (hAB : A < B) (hP : 0 < P) (hφA : P < φ A)
    (hr : 0 ≤ reserve)
    (hreserve : H ≤ cutPower φ P reserve (closedCut B h)-powerOffset-
      splitCoefficient*(φ B-P)^nu*(cutLogProduct φ P reserve (closedCut B h)-logOffset))
    (hL : let ps := orderedPositions h (eligibleIndices h Finset.univ A B)
      ∀ i ≤ ps.length, -E-δ*((countAbove h B : ℝ)+(i : ℝ)) ≤
        cutLogProduct φ P reserve (positionCut (fun _ b => decide (B ≤ b)) h (ps.take i))-logOffset) :
    let ps := orderedPositions h (eligibleIndices h Finset.univ A B)
    let w := eligibleRefinementWeights φ P h Finset.univ A B
    H-splitCoefficient*(E*(φ B-P)^nu+δ*((countAbove h B : ℝ)*(φ B-P)^nu+
      ∑ i ∈ Finset.range ps.length, w (i+1))) ≤ cutPower φ P reserve (fullCut A h)-powerOffset := by
  let ps := orderedPositions h (eligibleIndices h Finset.univ A B)
  let w := eligibleRefinementWeights φ P h Finset.univ A B
  let C := fun i => positionCut (fun _ b => decide (B ≤ b)) h (ps.take i)
  let k : ℕ → ℝ := fun i => (countAbove h B : ℝ)+(i : ℝ)
  have hs : C 0 = closedCut B h := by simp only [C,List.take_zero,positionCut_nil_closed]
  have he : C ps.length = fullCut A h := by
    change positionCut (fun _ b => decide (B ≤ b)) h (ps.take ps.length) = _
    rw [List.take_length]
    exact ordered_positionCut_final h hAB
  have hw0 : w 0 = (φ B-P)^nu := rfl
  have hend : w (ps.length+1) = 0 := eligibleRefinementWeights_end φ P h Finset.univ A B
  have hraw : cutPower φ P reserve (C 0)-splitCoefficient*w 0*cutLogProduct φ P reserve (C 0)+
      splitCoefficient*(∑ i ∈ Finset.range (ps.length+1), (w i-w (i+1))*cutLogProduct φ P reserve (C i)) ≤
      cutPower φ P reserve (C ps.length) := by
    simpa only [hs,he,w,eligibleRefinementWeights,refinementWeights_zero] using
      ordered_full_cut_weighted_lower φ hφ h hAB hP hφA hr
  have hshift := weighted_chain_shift (P := fun i => cutPower φ P reserve (C i))
    (L := fun i => cutLogProduct φ P reserve (C i)) (offset := logOffset) hend hraw
  have hchain : (cutPower φ P reserve (C 0)-powerOffset)-splitCoefficient*w 0*(cutLogProduct φ P reserve (C 0)-logOffset)+
      splitCoefficient*(∑ i ∈ Finset.range (ps.length+1), (w i-w (i+1))*(cutLogProduct φ P reserve (C i)-logOffset)) ≤
      cutPower φ P reserve (C ps.length)-powerOffset := by linear_combination hshift
  have hreserve' : H ≤ (cutPower φ P reserve (C 0)-powerOffset)-splitCoefficient*w 0*(cutLogProduct φ P reserve (C 0)-logOffset) := by
    simpa only [hs,hw0] using hreserve
  have hh := power_reserve_propagation (fun i => cutPower φ P reserve (C i)-powerOffset)
    (fun i => cutLogProduct φ P reserve (C i)-logOffset) w k split_coefficient_positive.le ps.length
    (fun i _ => eligibleRefinementWeights_decreasing hφ hφA hAB.le h Finset.univ i) hend
    (by intro i _; simp only [k,Nat.cast_add,Nat.cast_one]; ring) hL hreserve' hchain
  simpa only [he,k,Nat.cast_zero,add_zero,hw0] using hh

end
end StrongSilver
