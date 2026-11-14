-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CartesianBalanceRatios
import Mathlib.Analysis.Complex.Exponential

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 2400000

theorem ratio_close_of_log_close {x δ : ℝ} (hx : 0 < x) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (h : |Real.log x| ≤ δ) : |x-1| ≤ 2*δ := by
  have he := Real.abs_exp_sub_one_le (h.trans hδ1)
  rw [Real.exp_log hx] at he
  exact he.trans (mul_le_mul_of_nonneg_left h (by norm_num))

/-- Changing the offset from P to one preserves balance. The small
parameter is P/a; no comparison of unbounded absolute mass errors is used. -/
theorem offset_mass_balance {m P a δ : ℝ} (hm : 0 ≤ m) (hP : 1 ≤ P)
    (ha : P < a) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hPa : P ≤ δ*a)
    (hlog : |Real.log ((m+P)/(rho*(a-P)))| ≤ δ) :
    |(m+1)/(rho*a)-1| ≤ 4*δ := by
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  have ha0 : 0 < a := hP0.trans ha
  have ht : 0 < a-P := sub_pos.mpr ha
  have hden : 0 < rho*(a-P) := mul_pos rho_positive ht
  have hr1 : 1 < rho := by linarith only [rho_bounds.1]
  have hratio : 0 < (m+P)/(rho*(a-P)) := div_pos (by linarith only [hm,hP0]) hden
  have hclose := ratio_close_of_log_close hratio hδ hδ1 hlog
  have hscale : 0 ≤ (a-P)/a ∧ (a-P)/a ≤ 1 :=
    ⟨(div_pos ht ha0).le,(div_le_one ha0).mpr (by linarith only [hP0])⟩
  have hfirst : |((a-P)/a)*((m+P)/(rho*(a-P))-1)| ≤ 2*δ := by
    rw [abs_mul,abs_of_nonneg hscale.1]
    exact (mul_le_mul_of_nonneg_left hclose hscale.1).trans
      (by nlinarith only [hscale.2,hδ])
  have hsecond : |(1-(rho+1)*P)/(rho*a)| ≤ 2*δ := by
    rw [abs_div,abs_of_pos (mul_pos rho_positive ha0)]
    have hneg : 1-(rho+1)*P ≤ 0 := by nlinarith only [hP,hr1]
    rw [abs_of_nonpos hneg]
    apply (div_le_iff₀ (mul_pos rho_positive ha0)).mpr
    have hp := mul_le_mul_of_nonneg_left hPa (show 0 ≤ rho+1 by linarith only [hr1])
    have hδa : 0 ≤ δ*a := mul_nonneg hδ ha0.le
    have hrho := mul_le_mul_of_nonneg_right (show rho+1 ≤ 2*rho by linarith only [hr1]) hδa
    nlinarith only [hp,hrho]
  have he : (m+1)/(rho*a)-1 =
      ((a-P)/a)*((m+P)/(rho*(a-P))-1)+(1-(rho+1)*P)/(rho*a) := by
    field_simp [rho_positive.ne',ha0.ne',ht.ne'] <;> ring
  rw [he]
  exact (abs_add_le _ _).trans (by linarith only [hfirst,hsecond])

theorem offset_excess_balance {P a d δ : ℝ} (hP : 1 ≤ P) (ha : P < a)
    (hd : 0 ≤ d) (hδ : 0 ≤ δ) (hPa : P ≤ δ*a) (hdsmall : d ≤ δ*(a-P)) :
    |(a-1-d)/a-1| ≤ 2*δ := by
  have ha0 : 0 < a := (zero_lt_one.trans_le hP).trans ha
  have he : (a-1-d)/a-1 = -(1+d)/a := by field_simp; ring
  rw [he,abs_div,abs_neg,abs_of_nonneg (show 0 ≤ 1+d by linarith only [hd]),abs_of_pos ha0]
  apply (div_le_iff₀ ha0).mpr
  have hδP : 0 ≤ δ*P := mul_nonneg hδ (zero_le_one.trans hP)
  nlinarith only [hP,hPa,hdsmall,hδP]

namespace ScheduleTree

/-- The paper's log-ratio and drawdown balance conditions imply the
three offset-one ratios used in the actual Cartesian group construction. -/
theorem silverBalanced_of_log_balance {φ : ℝ → ℝ} {l r : ScheduleTree} {b P δ : ℝ}
    (hP : 1 ≤ P) (ha : P < φ b) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hPa : P ≤ δ*φ b)
    (hL : |Real.log ((Scalar.SignedIntervals.prefixMax (l.transformedWord φ)+P)/(rho*(φ b-P)))| ≤ δ)
    (hR : |Real.log ((Scalar.SignedIntervals.prefixMax (r.transformedWord φ)+P)/(rho*(φ b-P)))| ≤ δ)
    (hd : l.gapDrawdown φ ≤ δ*(φ b-P)) : SilverBalanced φ (4*δ) (.split l b r) := by
  refine ⟨(zero_lt_one.trans_le hP).trans ha,?_,?_,?_⟩
  · exact offset_mass_balance (Scalar.SignedIntervals.prefixMax_nonneg _) hP ha hδ hδ1 hPa hL
  · exact offset_mass_balance (Scalar.SignedIntervals.prefixMax_nonneg _) hP ha hδ hδ1 hPa hR
  · have h := offset_excess_balance hP ha (gapDrawdown_nonnegative φ l) hδ hPa hd
    exact h.trans (by nlinarith only [hδ])

end ScheduleTree
end
end StrongSilver
