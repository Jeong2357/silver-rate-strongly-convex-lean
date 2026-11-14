-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseLastTimeError
import StrongSilver.CappedTransform

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 2400000

theorem abs_log_le_twice_deviation {x : ℝ} (hx : 1/2 ≤ x) : |Real.log x| ≤ 2*|x-1| := by
  have hpos : 0 < x := by linarith only [hx]
  have hu := Real.log_le_sub_one_of_pos hpos
  have hl := Real.one_sub_inv_le_log_of_pos hpos
  have hi := inverse_deviation_half hx
  have ht := le_abs_self (x-1)
  have ht' := le_abs_self (x⁻¹-1)
  exact abs_le.mpr ⟨by linarith only [hl,hi,ht'],by linarith only [hu,ht,abs_nonneg (x-1)]⟩

theorem capped_step_error_le_square {μ B b : ℝ} (hμ : 0 < μ)
    (hB : 0 ≤ B) (hb : 0 ≤ b) (hμB : μ*B ≤ 1/2) :
    b ≤ cappedStep μ B b ∧ cappedStep μ B b-b ≤ 2*μ*b^2 := by
  obtain ⟨h0,h1⟩ := cappedStep_defect (b := b) hμ hμB
  have hmin := le_min hb hB
  have hminb := min_le_left b B
  have hsq : (min b B)^2 ≤ b^2 := by nlinarith only [hmin,hminb,hb]
  exact ⟨by linarith only [h0],h1.trans (mul_le_mul_of_nonneg_left hsq (by positivity))⟩

namespace FourPhase

/-- The exterior leading factor uses the same transformed excess as the
Cartesian telescoping product, even if the selected step exceeds the cap. -/
theorem last_excess_relative_error {μ T b d φ k : ℝ} (hμ : 0 < μ)
    (hT : 0 < T) (hb : 4 ≤ b) (hd : 0 ≤ d) (hdb : d ≤ b/4)
    (hφ : b ≤ φ) (hφerror : φ-b ≤ 2*μ*b^2)
    (herror : |T*k-(b-1-d)| ≤ μ*d^2+2*μ*b*d) :
    0 < φ-1-d ∧ |T*k/(φ-1-d)-1| ≤ 10*μ*b := by
  have hb0 : 0 < b := lt_of_lt_of_le (by norm_num) hb
  have hK : b/2 ≤ φ-1-d := by linarith only [hb,hdb,hφ]
  have hK0 : 0 < φ-1-d := by linarith only [hK,hb0]
  have hdiff : |T*k-(φ-1-d)| ≤ 5*μ*b^2 := by
    have he : T*k-(φ-1-d) = (T*k-(b-1-d))-(φ-b) := by ring
    have ht := abs_add_le (T*k-(b-1-d)) (-(φ-b))
    rw [abs_neg,abs_of_nonneg (sub_nonneg.mpr hφ)] at ht
    have hdb' : d ≤ b := by linarith only [hdb,hb0]
    have hd2 : d^2 ≤ b^2 := by nlinarith only [hd,hdb',hb0]
    have hbd := mul_le_mul_of_nonneg_left hdb' hb0.le
    have h1 := mul_le_mul_of_nonneg_left hd2 hμ.le
    have h2 := mul_le_mul_of_nonneg_left hbd hμ.le
    rw [he,sub_eq_add_neg]
    nlinarith only [ht,herror,hφerror,h1,h2]
  refine ⟨hK0,?_⟩
  have he : T*k/(φ-1-d)-1 = (T*k-(φ-1-d))/(φ-1-d) := by field_simp <;> ring
  rw [he,abs_div,abs_of_pos hK0]
  apply (div_le_iff₀ hK0).mpr
  have hp := mul_le_mul_of_nonneg_left hK (show 0 ≤ 10*μ*b by positivity)
  nlinarith only [hdiff,hp]

theorem last_excess_log_error {μ T b d φ k : ℝ} (hμ : 0 < μ)
    (hT : 0 < T) (hb : 4 ≤ b) (hd : 0 ≤ d) (hdb : d ≤ b/4)
    (hφ : b ≤ φ) (hφerror : φ-b ≤ 2*μ*b^2)
    (herror : |T*k-(b-1-d)| ≤ μ*d^2+2*μ*b*d) (hsmall : μ*b ≤ 1/100) :
    0 < φ-1-d ∧ 0 < k ∧ |Real.log (T*k/(φ-1-d))| ≤ 20*μ*b := by
  obtain ⟨hK,hdev⟩ := last_excess_relative_error hμ hT hb hd hdb hφ hφerror herror
  have hhalf : 1/2 ≤ T*k/(φ-1-d) := by
    have hh := (abs_le.mp hdev).1
    linarith only [hh,hsmall]
  have hkp : 0 < k := by
    have hratio : 0 < T*k/(φ-1-d) := by linarith only [hhalf]
    have hTk := (div_pos_iff.mp hratio).elim (fun h => h.1) (fun h => False.elim ((not_lt_of_ge hK.le) h.2))
    exact (mul_pos_iff.mp hTk).elim (fun h => h.2) (fun h => False.elim ((not_lt_of_ge hT.le) h.1))
  have hl := (abs_log_le_twice_deviation hhalf).trans (mul_le_mul_of_nonneg_left hdev (by norm_num))
  exact ⟨hK,hkp,by nlinarith only [hl]⟩

/-- A balanced group's exterior actual step gives the fixed lower bound
on k required by the joining construction. -/
theorem last_excess_lower_of_budget {μ T b d k : ℝ} (hμ : 0 < μ)
    (hT : 0 < T) (hb : 8 ≤ b) (hbT : (4/5:ℝ)*T ≤ b)
    (hd : 0 ≤ d) (hdb : d ≤ b/8) (hsmall : μ*b ≤ 1/100)
    (herror : |T*k-(b-1-d)| ≤ μ*d^2+2*μ*b*d) : 1/2 ≤ k := by
  have hdb4 : d ≤ b/4 := by linarith only [hdb,hb]
  have hφerror : b-b ≤ 2*μ*b^2 := by rw [sub_self]; positivity
  obtain ⟨hK,hdev⟩ := last_excess_relative_error hμ hT (by linarith only [hb]) hd hdb4 le_rfl hφerror herror
  have hratio : (9/10:ℝ) ≤ T*k/(b-1-d) := by
    have h := (abs_le.mp hdev).1
    linarith only [h,hsmall]
  have hprod := (le_div_iff₀ hK).mp hratio
  have hKlower : (3/4:ℝ)*b ≤ b-1-d := by linarith only [hdb,hb]
  have hTk : (1/2:ℝ)*T ≤ T*k := by nlinarith only [hprod,hKlower,hbT,hT]
  exact (mul_le_mul_iff_right₀ hT).mp (by nlinarith only [hTk])

end FourPhase
end
end StrongSilver
