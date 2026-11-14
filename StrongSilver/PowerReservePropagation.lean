-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.WeightedTelescoping
import StrongSilver.RefinementWeights
import StrongSilver.PositionCuts

namespace StrongSilver
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1600000

theorem sum_stepAt (xs : List ℝ) : (∑ i ∈ Finset.range xs.length, stepAt xs i) = xs.sum := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    rw [List.length_cons,Finset.sum_range_succ']
    change (∑ i ∈ Finset.range xs.length, stepAt xs i)+a = a+xs.sum
    rw [ih]
    ring

theorem sum_refinementWeights (b : ℝ) (xs : List ℝ) :
    (∑ i ∈ Finset.range xs.length, refinementWeights b xs (i+1)) = xs.sum := sum_stepAt xs

theorem position_cut_count_after (base : ℕ → ℝ → Bool) (h : List ℝ) (ps : List ℕ)
    (hnd : ps.Nodup) (hvalid : ∀ p ∈ ps, p < h.length)
    (hfalse : ∀ p (hp : p ∈ ps), base p (h[p]'(hvalid p hp)) = false) :
    ∀ n ≤ ps.length, (positionCut base h (ps.take n)).phases.length = (positionCut base h []).phases.length+n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    intro hn
    have hlt : n < ps.length := by omega
    obtain ⟨I,ho,hnew,hpivot⟩ := exists_position_chain_insertion base h ps hnd hvalid hfalse n hlt
    have hs := I.selected_count_increment
    rw [ho,hnew] at hs
    have hp := ih (by omega)
    omega

/-- The initial positive reserve survives refinement once the uniform and
selected-count logarithmic errors are charged by summation by parts. -/
theorem power_reserve_propagation (P L w k : ℕ → ℝ) {c H E δ : ℝ} (hc : 0 ≤ c) (n : ℕ)
    (hw : ∀ i ≤ n, w (i+1) ≤ w i) (hend : w (n+1) = 0)
    (hk : ∀ i < n, k (i+1) = k i+1) (hL : ∀ i ≤ n, -E-δ*k i ≤ L i)
    (hreserve : H ≤ P 0-c*w 0*L 0)
    (hchain : P 0-c*w 0*L 0+c*(∑ i ∈ Finset.range (n+1), (w i-w (i+1))*L i) ≤ P n) :
    H-c*(E*w 0+δ*(k 0*w 0+∑ i ∈ Finset.range n, w (i+1))) ≤ P n := by
  have hlog := weighted_log_lower w L k E δ n hw hend hL
  rw [weighted_count_identity w k n hk hend] at hlog
  have hs := mul_le_mul_of_nonneg_left hlog hc
  nlinarith only [hs,hreserve,hchain]

end
end StrongSilver
