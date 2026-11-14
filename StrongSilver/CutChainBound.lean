-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PositionCuts
import StrongSilver.WeightedTelescoping

namespace StrongSilver
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1800000

/-- One step of a chronological-position refinement satisfies the scalar
power/log bound on the actual before and after cuts. -/
theorem position_chain_power_log_step (φ : ℝ → ℝ) (base : ℕ → ℝ → Bool) (h : List ℝ) (ps : List ℕ)
    {P reserve : ℝ} (hP : 0 < P) (hr : 0 ≤ reserve)
    (hnd : ps.Nodup) (hvalid : ∀ p ∈ ps, p < h.length)
    (hfalse : ∀ p (hp : p ∈ ps), base p (h[p]'(hvalid p hp)) = false)
    (hpiv : ∀ p (hp : p ∈ ps), P < φ (h[p]'(hvalid p hp))) (i : ℕ) (hi : i < ps.length) :
    cutPower φ P reserve (positionCut base h (ps.take i))-
        cutPower φ P reserve (positionCut base h (ps.take (i+1))) ≤
      splitCoefficient*(φ (h[ps[i]]'(hvalid ps[i] (List.getElem_mem hi)))-P)^nu*
        (cutLogProduct φ P reserve (positionCut base h (ps.take i))-
          cutLogProduct φ P reserve (positionCut base h (ps.take (i+1)))) := by
  obtain ⟨I,ho,hn,hb⟩ := exists_position_chain_insertion base h ps hnd hvalid hfalse i hi
  have hh := I.power_log_control φ hP hr (by rw [hb]; exact hpiv ps[i] (List.getElem_mem hi))
  simpa only [ho,hn,hb] using hh

/-- The weighted split-chain lower bound is realized by actual index
insertions, rather than postulated changes of a numerical potential. -/
theorem position_chain_weighted_lower (φ : ℝ → ℝ) (base : ℕ → ℝ → Bool) (h : List ℝ) (ps : List ℕ)
    {P reserve : ℝ} (hP : 0 < P) (hr : 0 ≤ reserve)
    (hnd : ps.Nodup) (hvalid : ∀ p ∈ ps, p < h.length)
    (hfalse : ∀ p (hp : p ∈ ps), base p (h[p]'(hvalid p hp)) = false)
    (hpiv : ∀ p (hp : p ∈ ps), P < φ (h[p]'(hvalid p hp))) (w : ℕ → ℝ)
    (hw : ∀ i (hi : i < ps.length), w (i+1) = (φ (h[ps[i]]'(hvalid ps[i] (List.getElem_mem hi)))-P)^nu)
    (hend : w (ps.length+1) = 0) :
    cutPower φ P reserve (positionCut base h [])-
        splitCoefficient*w 0*cutLogProduct φ P reserve (positionCut base h [])+
      splitCoefficient*(∑ i ∈ Finset.range (ps.length+1), (w i-w (i+1))*
        cutLogProduct φ P reserve (positionCut base h (ps.take i))) ≤
      cutPower φ P reserve (positionCut base h ps) := by
  have hh := weighted_split_chain_lower
    (fun i => cutPower φ P reserve (positionCut base h (ps.take i)))
    (fun i => cutLogProduct φ P reserve (positionCut base h (ps.take i))) w splitCoefficient ps.length
    (by
      intro i hi
      rw [hw i hi]
      exact position_chain_power_log_step φ base h ps hP hr hnd hvalid hfalse hpiv i hi) hend
  simpa only [List.take_zero,List.take_length] using hh

end
end StrongSilver
