-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CutInsertionExcess
import StrongSilver.PositionCuts
import StrongSilver.OrderedPositions
import StrongSilver.WeightedExcessChain

namespace StrongSilver
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2800000

/-- Exact excess at each actual chronological-position insertion. -/
def positionCutExcess (φ : ℝ → ℝ) (P reserve : ℝ) (base : ℕ → ℝ → Bool)
    (h : List ℝ) (ps : List ℕ) (i : ℕ) : ℝ :=
  splitCoefficient*(φ (stepAt h (ps[i]?.getD 0))-P)^nu*
    (cutLogProduct φ P reserve (positionCut base h (ps.take i))-
      cutLogProduct φ P reserve (positionCut base h (ps.take (i+1))))-
    (cutPower φ P reserve (positionCut base h (ps.take i))-
      cutPower φ P reserve (positionCut base h (ps.take (i+1))))

/-- Every term is the excess of a genuine padded signed-word split. -/
theorem positionCutExcess_realized (φ : ℝ → ℝ) (base : ℕ → ℝ → Bool) (h : List ℝ) (ps : List ℕ)
    {P reserve : ℝ} (hP : 0 < P) (hr : 0 ≤ reserve)
    (hnd : ps.Nodup) (hvalid : ∀ p ∈ ps, p < h.length)
    (hfalse : ∀ p (hp : p ∈ ps), base p (h[p]'(hvalid p hp)) = false)
    (hpiv : ∀ p (hp : p ∈ ps), P < φ (h[p]'(hvalid p hp))) (i : ℕ) (hi : i < ps.length) :
    ∃ S : PaddedSplitInput,
      S.weight = (φ (stepAt h (ps[i]?.getD 0))-P)^nu ∧
      S.excess = positionCutExcess φ P reserve base h ps i := by
  obtain ⟨I,ho,hn,hb⟩ := exists_position_chain_insertion base h ps hnd hvalid hfalse i hi
  have hpi : P < φ I.pivot := by rw [hb]; exact hpiv ps[i] (List.getElem_mem hi)
  let S := I.splitInput φ hP hr hpi
  have hstep : stepAt h (ps[i]?.getD 0) = h[ps[i]]'(hvalid ps[i] (List.getElem_mem hi)) := by
    simp only [List.getElem?_eq_getElem hi,Option.getD_some]
    exact stepAt_eq (hvalid ps[i] (List.getElem_mem hi))
  refine ⟨S,?_,?_⟩
  · change (φ I.pivot-P)^nu = _
    rw [hb,hstep]
  · have hh := I.split_excess_identity φ hP hr hpi
    simpa only [ho,hn,hb,positionCutExcess,hstep] using hh

theorem positionCutExcess_nonnegative (φ : ℝ → ℝ) (base : ℕ → ℝ → Bool) (h : List ℝ) (ps : List ℕ)
    {P reserve : ℝ} (hP : 0 < P) (hr : 0 ≤ reserve)
    (hnd : ps.Nodup) (hvalid : ∀ p ∈ ps, p < h.length)
    (hfalse : ∀ p (hp : p ∈ ps), base p (h[p]'(hvalid p hp)) = false)
    (hpiv : ∀ p (hp : p ∈ ps), P < φ (h[p]'(hvalid p hp))) (i : ℕ) (hi : i < ps.length) :
    0 ≤ positionCutExcess φ P reserve base h ps i := by
  obtain ⟨S,hw,he⟩ := positionCutExcess_realized φ base h ps hP hr hnd hvalid hfalse hpiv i hi
  rw [← he]
  exact S.excess_nonnegative

end
end StrongSilver
