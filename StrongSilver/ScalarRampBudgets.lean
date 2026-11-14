-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ScalarRampBounds
import StrongSilver.LogConsequences

namespace StrongSilver
open Real Set
noncomputable section
set_option maxHeartbeats 1000000

theorem scalarNegativeProduct_eq_exp {T : ℝ} (hT : 0 < T) (h : List ℝ) :
    scalarNegativeProduct (1/T) h = Real.exp (negativeLogSum h T) := by
  induction h with
  | nil => simp [scalarNegativeProduct,negativeLogSum]
  | cons b h ih =>
    change scalarNegativeFactor (1/T) b*scalarNegativeProduct (1/T) h =
      Real.exp ((if b < 0 then Real.log (1+|b|/T) else 0)+negativeLogSum h T)
    rw [Real.exp_add,ih]
    congr 1
    by_cases hb : b < 0
    · rw [if_pos hb,Real.exp_log (by positivity : 0 < 1+|b|/T)]
      simp only [scalarNegativeFactor,max_eq_left (by linarith : 0 ≤ -b),abs_of_neg hb]
      ring
    · simp only [scalarNegativeFactor,if_neg hb,Real.exp_zero,
        max_eq_right (by linarith : -b ≤ 0),mul_zero,add_zero]

theorem scalarBackwardFactor_exp_bound {s A b : ℝ} (hs : 0 ≤ s) (hA : s*A < 1)
    (hb : 0 < b → b ≤ A) :
    scalarBackwardFactor s b ≤ Real.exp (s*max b 0/(1-s*A)) := by
  by_cases hneg : b ≤ 0
  · simp only [scalarBackwardFactor,if_pos hneg,max_eq_right hneg,mul_zero,zero_div,Real.exp_zero,le_refl]
  · have hbpos : 0 < b := lt_of_not_ge hneg
    have hsb : s*b ≤ s*A := mul_le_mul_of_nonneg_left (hb hbpos) hs
    have hd : 0 < 1-s*b := by linarith
    have hdA : 0 < 1-s*A := by linarith
    have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hd)
    rw [Real.log_inv] at hlog
    have hid : (1-s*b)⁻¹-1 = s*b/(1-s*b) := by field_simp [hd.ne']; ring
    rw [hid] at hlog
    have hfrac : s*b/(1-s*b) ≤ s*b/(1-s*A) := by
      gcongr
    have he : (1-s*b)⁻¹ = Real.exp (-Real.log (1-s*b)) := by rw [Real.exp_neg,Real.exp_log hd]
    rw [scalarBackwardFactor,if_neg hneg,max_eq_left hbpos.le,he]
    exact Real.exp_le_exp.mpr (hlog.trans hfrac)

theorem scalarBackwardProduct_exp_bound {s A : ℝ} (hs : 0 ≤ s) (hA : s*A < 1)
    (h : List ℝ) (hh : ∀ b ∈ h, 0 < b → b ≤ A) :
    scalarBackwardProduct s h ≤ Real.exp (s*Scalar.SignedIntervals.positiveMass h/(1-s*A)) := by
  induction h with
  | nil => simp [scalarBackwardProduct,Scalar.SignedIntervals.positiveMass]
  | cons b h ih =>
    have hb := scalarBackwardFactor_exp_bound hs hA (hh b List.mem_cons_self)
    have ht := ih (fun c hc => hh c (List.mem_cons_of_mem b hc))
    have hf : 0 ≤ scalarBackwardFactor s b := by
      unfold scalarBackwardFactor
      split_ifs with hneg
      · exact zero_le_one
      · have hsb := mul_le_mul_of_nonneg_left (hh b List.mem_cons_self (lt_of_not_ge hneg)) hs
        exact inv_nonneg.mpr (by linarith)
    have hp := mul_le_mul hb ht (List.prod_nonneg (by
      intro v hv
      obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hv
      unfold scalarBackwardFactor
      split_ifs with hneg
      · exact zero_le_one
      · have hsc := mul_le_mul_of_nonneg_left (hh c (List.mem_cons_of_mem b hc) (lt_of_not_ge hneg)) hs
        exact inv_nonneg.mpr (by linarith))) (Real.exp_pos _).le
    change scalarBackwardFactor s b*scalarBackwardProduct s h ≤
      Real.exp (s*(max b 0+Scalar.SignedIntervals.positiveMass h)/(1-s*A))
    calc
      _ ≤ Real.exp (s*max b 0/(1-s*A))*Real.exp (s*Scalar.SignedIntervals.positiveMass h/(1-s*A)) := hp
      _ = _ := by rw [← Real.exp_add]; congr 1; ring

end
end StrongSilver
