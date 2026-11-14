-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.QuadraticBudget

namespace StrongSilver
noncomputable section

def negativeLogSum (h : List ℝ) (s : ℝ) : ℝ :=
  (h.map (fun b => if b < 0 then Real.log (1+|b|/s) else 0)).sum
def largeLogSum (h : List ℝ) (s : ℝ) : ℝ :=
  (h.map (fun b => if s ≤ b then Real.log (b/s) else 0)).sum
def largeLogESum (h : List ℝ) (s : ℝ) : ℝ :=
  (h.map (fun b => if s ≤ b then Real.log (Real.exp 1+b) else 0)).sum

theorem logGain_ratio {s : ℝ} (hs : 0 < s) (b : ℝ) :
    logGain (b/s) = (if b < 0 then Real.log (1+|b|/s) else 0)+
      (if s ≤ b then Real.log (b/s) else 0) := by
  by_cases hb : b < 0
  · have hx : b/s < 0 := div_neg_of_neg_of_pos hb hs
    have hsb : ¬s ≤ b := by linarith
    simp only [logGain,if_pos hx,if_pos hb,if_neg hsb,add_zero,abs_of_neg hb]
    congr 1
    ring
  · have hx : ¬b/s < 0 := not_lt_of_ge (div_nonneg (le_of_not_gt hb) hs.le)
    rw [logGain,if_neg hx,if_neg hb,zero_add]
    simp only [one_le_div hs]

theorem logGains_eq {s : ℝ} (hs : 0 < s) (h : List ℝ) :
    logGains h s = negativeLogSum h s+largeLogSum h s := by
  induction h with
  | nil => simp [logGains,negativeLogSum,largeLogSum]
  | cons b h ih =>
    simp only [logGains,negativeLogSum,largeLogSum,List.map_cons,List.sum_cons] at *
    rw [logGain_ratio hs b]
    linarith only [ih]

theorem combined_log_budget : ∃ C > 0, ∀ κ s cap : ℝ, 1 < κ → 4 ≤ s → s ≤ κ → s ≤ cap →
    ∀ h : List ℝ, -Real.log (D κ h).toReal/2+negativeLogSum h s+largeLogSum h s ≤
      C*weightedCount h cap*s^(-nu) := by
  obtain ⟨C,hC,hb⟩ := scalar_log_budget
  refine ⟨C,hC,fun κ s cap hκ hs hsκ hcap h => ?_⟩
  have hspos : 0 < s := lt_of_lt_of_le (by norm_num) hs
  have hh := hb κ s cap hκ hs hsκ hcap h
  rw [logGains_eq hspos h] at hh
  linarith only [hh]

theorem stable_logGains_bound : ∃ C > 0, ∀ κ s cap : ℝ, 1 < κ → 4 ≤ s → s ≤ κ → s ≤ cap →
    ∀ h : List ℝ, D κ h ≤ 1 → logGains h s ≤ C*weightedCount h cap*s^(-nu) := by
  obtain ⟨C,hC,hb⟩ := scalar_log_budget
  refine ⟨C,hC,fun κ s cap hκ hs hsκ hcap h hD => ?_⟩
  have hDr : (D κ h).toReal ≤ 1 := by simpa using ENNReal.toReal_mono ENNReal.one_ne_top hD
  have hl := Real.log_nonpos ENNReal.toReal_nonneg hDr
  have hh := hb κ s cap hκ hs hsκ hcap h
  linarith

theorem large_log_e_point {s b : ℝ} (hs : 0 < s) (hb : s ≤ b) :
    Real.log (Real.exp 1+b) ≤ Real.log (Real.exp 1+s)+Real.log (b/s) := by
  have hbpos : 0 < b := hs.trans_le hb
  have hbase : 0 < Real.exp 1+s := by positivity
  have hx : 1 ≤ b/s := (one_le_div hs).mpr hb
  have he : Real.exp 1+b ≤ (Real.exp 1+s)*(b/s) := by
    have hh := mul_le_mul_of_nonneg_left hx (Real.exp_pos 1).le
    have hc : s*(b/s) = b := by field_simp
    nlinarith only [hh,hc]
  have hl := Real.log_le_log (by positivity : 0 < Real.exp 1+b) he
  rwa [Real.log_mul hbase.ne' (div_pos hbpos hs).ne'] at hl

theorem largeLogESum_le {s : ℝ} (hs : 0 < s) (h : List ℝ) :
    largeLogESum h s ≤ (countAbove h s : ℝ)*Real.log (Real.exp 1+s)+largeLogSum h s := by
  induction h with
  | nil => simp [largeLogESum,largeLogSum]
  | cons b h ih =>
    simp only [largeLogESum,largeLogSum,List.map_cons,List.sum_cons,countAbove_cons,Nat.cast_add] at *
    by_cases hb : s ≤ b
    · simp only [if_pos hb,Nat.cast_one] at *
      have hp := large_log_e_point hs hb
      nlinarith only [ih,hp]
    · simp only [if_neg hb,Nat.cast_zero,zero_add,zero_mul] at *
      exact ih

/-- Equation (2.6), for an arbitrary predetermined real schedule with D≤1. -/
theorem stable_large_log_e_bound : ∃ C > 0, ∀ κ s cap : ℝ, 1 < κ → 4 ≤ s → s ≤ κ → s ≤ cap →
    ∀ h : List ℝ, D κ h ≤ 1 → largeLogESum h s ≤
      C*weightedCount h cap*s^(-nu)*Real.log (Real.exp 1+s) := by
  obtain ⟨C,hC,hb⟩ := stable_logGains_bound
  refine ⟨C+1,by linarith,fun κ s cap hκ hs hsκ hcap h hD => ?_⟩
  have hspos : 0 < s := lt_of_lt_of_le (by norm_num) hs
  have hn := countAbove_rank_bound h hspos hcap
  have hgain := hb κ s cap hκ hs hsκ hcap h hD
  have hG : largeLogSum h s ≤ logGains h s := by
    rw [logGains_eq hspos]
    have hN : 0 ≤ negativeLogSum h s := by
      apply List.sum_nonneg
      intro x hx
      obtain ⟨b,hbm,rfl⟩ := List.mem_map.mp hx
      split_ifs
      · exact Real.log_nonneg (by
          have hh : 0 ≤ |b|/s := div_nonneg (abs_nonneg _) hspos.le
          linarith)
      · exact le_rfl
    linarith
  have hlog : 1 ≤ Real.log (Real.exp 1+s) := by
    have hh := Real.log_le_log (Real.exp_pos 1) (show Real.exp 1 ≤ Real.exp 1+s by linarith)
    simpa only [Real.log_exp] using hh
  have hr := largeLogESum_le hspos h
  have hcount := mul_le_mul_of_nonneg_right hn (by linarith : 0 ≤ Real.log (Real.exp 1+s))
  have hterm := mul_le_mul_of_nonneg_left hlog
    (mul_nonneg (mul_nonneg hC.le (weightedCount_nonneg h cap)) (Real.rpow_nonneg hspos.le (-nu)))
  nlinarith only [hr,hcount,hG,hgain,hterm]

end
end StrongSilver
