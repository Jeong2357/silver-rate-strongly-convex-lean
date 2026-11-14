-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.EligibleWeights
import StrongSilver.CutChainBound

namespace StrongSilver
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2000000

/-- Equation (3.34) for the full cut: actual eligible positions are sorted
by decreasing step and increasing index, inserted once, and assigned their
actual transformed pivot weights. -/
theorem ordered_full_cut_weighted_lower (φ : ℝ → ℝ) (hφ : Monotone φ) (h : List ℝ)
    {A B P reserve : ℝ} (hAB : A < B) (hP : 0 < P) (hφA : P < φ A) (hr : 0 ≤ reserve) :
    let ps := orderedPositions h (eligibleIndices h Finset.univ A B)
    let w := eligibleRefinementWeights φ P h Finset.univ A B
    cutPower φ P reserve (closedCut B h)-splitCoefficient*(φ B-P)^nu*cutLogProduct φ P reserve (closedCut B h)+
      splitCoefficient*(∑ i ∈ Finset.range (ps.length+1), (w i-w (i+1))*
        cutLogProduct φ P reserve (positionCut (fun _ b => decide (B ≤ b)) h (ps.take i))) ≤
      cutPower φ P reserve (fullCut A h) := by
  let E := eligibleIndices h Finset.univ A B
  let ps := orderedPositions h E
  let base : ℕ → ℝ → Bool := fun _ b => decide (B ≤ b)
  let w := eligibleRefinementWeights φ P h Finset.univ A B
  have hnd := orderedPositions_nodup h E
  have hvalid : ∀ p ∈ ps, p < h.length := orderedPositions_valid h E
  have hfalse : ∀ p (hp : p ∈ ps), base p (h[p]'(hvalid p hp)) = false := by
    intro p hp
    have hb := (eligible_positions_range h Finset.univ A B p hp).2
    rw [stepAt_eq (hvalid p hp)] at hb
    simp only [base,not_le.mpr hb,decide_false]
  have hpiv : ∀ p (hp : p ∈ ps), P < φ (h[p]'(hvalid p hp)) := by
    intro p hp
    have ha := (eligible_positions_range h Finset.univ A B p hp).1
    rw [stepAt_eq (hvalid p hp)] at ha
    exact hφA.trans_le (hφ ha.le)
  have hw : ∀ i (hi : i < ps.length), w (i+1) = (φ (h[ps[i]]'(hvalid ps[i] (List.getElem_mem hi)))-P)^nu := by
    intro i hi
    have hh := eligibleRefinementWeights_step φ P h Finset.univ A B hi
    rw [stepAt_eq (hvalid ps[i] (List.getElem_mem hi))] at hh
    exact hh
  have hend : w (ps.length+1) = 0 := eligibleRefinementWeights_end φ P h Finset.univ A B
  have hh := position_chain_weighted_lower φ base h ps hP hr hnd hvalid hfalse hpiv w hw hend
  have hstart : positionCut base h [] = closedCut B h := positionCut_nil_closed h B
  have hfinal : positionCut base h ps = fullCut A h := ordered_positionCut_final h hAB
  have hw0 : w 0 = (φ B-P)^nu := rfl
  rw [hstart,hfinal,hw0] at hh
  exact hh

end
end StrongSilver
