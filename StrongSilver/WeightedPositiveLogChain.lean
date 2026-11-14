-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.WeightedExcessChain

namespace StrongSilver
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2800000

/-- Finite weighted positive-log estimate behind (4.10). Applied to the
positive-part transform, it bounds the integral of (L^S-log κ)^+ by the
endpoint power and log budgets. -/
theorem weighted_positive_log_chain_bound (P L w : ℕ → ℝ) (n : ℕ) {c M e : ℝ}
    (hc : 0 ≤ c) (he : 0 ≤ e)
    (hw : ∀ i ≤ n, 0 < w i) (hmono : ∀ i < n, w (i+1) ≤ w i)
    (hlower : ∀ i ≤ n, -e ≤ w i*L i)
    (hupper : w 0*L 0 ≤ M) (hP0 : 0 ≤ P 0) (hPn : P n ≤ M)
    (hjump : ∀ i < n, P i-P (i+1) ≤ c*w (i+1)*(L i-L (i+1))) :
    c*(∑ i ∈ Finset.range n, (w i-w (i+1))*max (L i) 0) ≤
      c*(M+e+e*(Real.log (w 0)-Real.log (w n)))+M := by
  have hpoint : ∀ i < n, (w i-w (i+1))*max (L i) 0 ≤
      (w i-w (i+1))*L i+e*((w i-w (i+1))/w i) := by
    intro i hi
    have hwi := hw i (by omega)
    have hl := hlower i (by omega)
    have hm : max (L i) 0 ≤ L i+e/w i := by
      apply max_le
      · have hh := div_nonneg he hwi.le
        linarith only [hh]
      · have hd : -L i ≤ e/w i := (le_div_iff₀ hwi).mpr (by nlinarith only [hl])
        linarith only [hd]
    have hp := mul_le_mul_of_nonneg_left hm (sub_nonneg.mpr (hmono i hi))
    have hid : (w i-w (i+1))*(L i+e/w i) =
        (w i-w (i+1))*L i+e*((w i-w (i+1))/w i) := by ring
    rwa [hid] at hp
  have hs := Finset.sum_le_sum (s := Finset.range n) (fun i hi => hpoint i (Finset.mem_range.mp hi))
  rw [Finset.sum_add_distrib,← Finset.mul_sum] at hs
  have hpower := Finset.sum_le_sum (s := Finset.range n) (fun i hi => hjump i (Finset.mem_range.mp hi))
  have hsum : (∑ i ∈ Finset.range n, c*w (i+1)*(L i-L (i+1))) =
      c*(∑ i ∈ Finset.range n, w (i+1)*(L i-L (i+1))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [sum_successive_differences,hsum,weighted_difference_endpoints] at hpower
  have hlast := hlower n le_rfl
  have hlog := mul_le_mul_of_nonneg_left (relative_weight_drop_sum w n hw) he
  have hs' := mul_le_mul_of_nonneg_left hs hc
  have hlog' := mul_le_mul_of_nonneg_left hlog hc
  have hu := mul_le_mul_of_nonneg_left hupper hc
  have hl := mul_le_mul_of_nonneg_left hlast hc
  nlinarith only [hpower,hs',hlog',hu,hl,hP0,hPn]

end
end StrongSilver
