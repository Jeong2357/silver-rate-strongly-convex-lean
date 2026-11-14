-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ScalarRampSuffix

namespace StrongSilver.ScalarRamp
open Set Real
noncomputable section
variable (R : ScalarRamp)
set_option maxHeartbeats 1000000

theorem uniform_state_estimates {μ T A b e : ℝ} (hT : 0 < T) (hb : 0 < b) (he : 0 < e)
    (hAT : A < T) (hbase : R.base = 1/T) (ha : R.amplitude ≤ e/b)
    (hv : e/2 ≤ R.threshold) (hve : R.threshold ≤ e)
    (hμ0 : 0 ≤ μ) (hμ1 : μ < 1) (hμb : μ ≤ R.base) (hμhalf : μ ≤ 1/2)
    (h : List ℝ) (hh : ∀ c ∈ h, 0 < c → c ≤ A) (x : ℝ)
    (hend : iterate h R.physical x = e)
    (hstates : ∀ j : ℕ, j ≤ h.length → 0 < iterate (h.take j) R.physical x)
    (i : ℕ) (hi : i ≤ h.length) :
    let t := iterate (h.take i) R.physical x
    let S := R.contraction hμ0 hμ1 hμb
    (e/2)*Real.exp (-negativeLogSum h T) ≤ t ∧
    t ≤ scalarRampGrowth T A b h*e ∧
    0 ≤ S.g t ∧ S.g t ≤ 2*(scalarRampGrowth T A b h/T+1/b)*e ∧
    ((1/T-μ)/32)*Real.exp (-2*negativeLogSum h T)*e^2 ≤ S.potential (S.proximalMap t) := by
  let t := iterate (h.take i) R.physical x
  let S := R.contraction hμ0 hμ1 hμb
  have ht : 0 < t := hstates i hi
  obtain ⟨hrun,hsts⟩ := positive_trajectory_suffix h R.physical x e he hend hstates i
  have hl := R.source_lower_exp hT hbase (h.drop i) t e hve hrun hsts
  have hu := R.source_upper_exp hT hb hAT hbase ha (h.drop i)
    (fun c hc => hh c (List.mem_of_mem_drop hc)) t hrun hsts
  have hneg := negativeLogSum_drop_le hT h i
  have hgrowth := scalarRampGrowth_drop_le hT hb hAT h i
  have hL : (e/2)*Real.exp (-negativeLogSum h T) ≤ t := by
    have hexp := Real.exp_le_exp.mpr (neg_le_neg hneg)
    have hm := mul_le_mul hv hexp (Real.exp_pos _).le R.threshold_nonnegative
    exact hm.trans hl
  have hU : t ≤ scalarRampGrowth T A b h*e := hu.trans (mul_le_mul_of_nonneg_right hgrowth he.le)
  have hg0 : 0 ≤ S.g t := by
    have hh := S.monotone ht.le
    rwa [S.zero] at hh
  have hg := R.contraction_slope_upper hμ0 hμ1 hμb hμhalf ht.le
  have hquot := mul_le_mul_of_nonneg_left hU (one_div_pos.mpr hT).le
  have hgU : S.g t ≤ 2*(scalarRampGrowth T A b h/T+1/b)*e := by
    rw [hbase] at hg
    simp only [div_eq_mul_inv] at ha hg hquot ⊢
    nlinarith only [hg,hquot,ha]
  have hp := R.proximal_potential_height hμ0 hμ1 hμb ht.le
  have hL0 : 0 ≤ (e/2)*Real.exp (-negativeLogSum h T) := mul_nonneg (by linarith) (Real.exp_pos _).le
  have hsq : ((e/2)*Real.exp (-negativeLogSum h T))^2 ≤ t^2 := by nlinarith only [hL,hL0]
  have hm := mul_le_mul_of_nonneg_left hsq (show 0 ≤ (R.base-μ)/8 by linarith)
  have hexp : Real.exp (-negativeLogSum h T)^2 = Real.exp (-2*negativeLogSum h T) := by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  have heq : ((R.base-μ)/8)*((e/2)*Real.exp (-negativeLogSum h T))^2 =
      ((1/T-μ)/32)*Real.exp (-2*negativeLogSum h T)*e^2 := by
    rw [mul_pow,hexp,hbase]
    ring
  rw [heq] at hm
  exact ⟨hL,hU,hg0,hgU,hm.trans hp⟩

end
end StrongSilver.ScalarRamp
