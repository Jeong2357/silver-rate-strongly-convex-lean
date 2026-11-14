-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.InitialMarkedRank
import StrongSilver.PowerLogDecay

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 2400000

/-- The initial reserved-block logarithmic price remains small uniformly
in B/(a*kappa), including cutoffs arbitrarily far below the cap. -/
theorem initial_marked_log_budget {a κ B : ℝ} (ha : 0 < a) (ha1 : a ≤ 1/128)
    (hκ : 0 < κ) (hcap : 1 ≤ a*κ) (hB : 0 < B) (hBcap : B ≤ a*κ)
    (C : ScheduleCut) (hgap : ∀ b ∈ C.unselected, 0 < b → b ≤ B) (hD : D κ C.word ≤ 1) :
    B^nu*(badPhaseCount (initialPhaseTests κ) C.phases : ℝ)*(1+Real.log (κ/B)) ≤
      weightedCount C.word (a*κ)*(initialMarkedRankConstant*Real.sqrt a*(1+Real.log (1/a)+1/nu)+
        (a/(1-nu))*(2+Real.log (1/a))) := by
  have haone : a ≤ 1 := ha1.trans (by norm_num)
  have hc := mul_pos ha hκ
  have hcκ : a*κ ≤ κ := by nlinarith only [haone,hκ]
  have hBκ := hBcap.trans hcκ
  have hF : 0 ≤ 1+Real.log (κ/B) := by
    have hh := Real.log_nonneg ((one_le_div hB).mpr hBκ)
    linarith only [hh]
  have hj := initial_marked_rank_bound ha ha1 hκ hcap hB hBcap C hgap hD
  have hs := mul_le_mul_of_nonneg_right hj (mul_nonneg (Real.rpow_pos_of_pos hB nu).le hF)
  have hq := cutoff_rpow_log_bound hB hBcap hcκ nu_positive
  have hq1 := cutoff_rpow_log_bound hB hBcap hcκ (by norm_num : (0 : ℝ) < 1)
  simp only [Real.rpow_one,div_one] at hq1
  have he : κ/(a*κ) = 1/a := by field_simp
  rw [he] at hq hq1
  have hp : B^nu*(a*κ)^(-nu) = (B/(a*κ))^nu := by
    rw [Real.rpow_neg hc.le,Real.div_rpow hB.le hc.le,div_eq_mul_inv]
  have hb : B^nu*B^(1-nu) = B := by
    rw [← Real.rpow_add hB,show nu+(1-nu) = (1 : ℝ) by ring,Real.rpow_one]
  have heq : B^nu*(initialMarkedRankConstant*Real.sqrt a*weightedCount C.word (a*κ)*(a*κ)^(-nu)+
      (weightedCount C.word (a*κ)*B^(1-nu)/(1-nu))/κ)*(1+Real.log (κ/B)) =
      weightedCount C.word (a*κ)*(initialMarkedRankConstant*Real.sqrt a*((B/(a*κ))^nu*(1+Real.log (κ/B)))+
        (a/(1-nu))*((B/(a*κ))*(1+Real.log (κ/B)))) := by
    calc
      _ = initialMarkedRankConstant*Real.sqrt a*weightedCount C.word (a*κ)*(B^nu*(a*κ)^(-nu))*(1+Real.log (κ/B))+
          (B^nu*B^(1-nu))*weightedCount C.word (a*κ)/(1-nu)/κ*(1+Real.log (κ/B)) := by ring
      _ = _ := by rw [hp,hb]; field_simp <;> ring
  have hfirst := mul_le_mul_of_nonneg_left hq (mul_nonneg initialMarkedRankConstant_positive.le (Real.sqrt_nonneg a))
  have hsecond := mul_le_mul_of_nonneg_left hq1 (div_nonneg ha.le (by linarith [nu_lt_one] : 0 ≤ 1-nu))
  have htotal := mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) (weightedCount_nonneg C.word (a*κ))
  rw [← heq] at htotal
  nlinarith only [hs,htotal]

end
end StrongSilver
