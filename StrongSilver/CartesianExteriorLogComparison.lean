-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseLastRelativeError

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 3000000

/-- Compare the exact transformed exterior factor with the ordinary
reference factor. The offset-one denominator only improves the ratio.
The only loss is proportional to drawdown divided by the selected step. -/
theorem exterior_factor_log_comparison {m P b φ d : ℝ} (hm : 0 ≤ m) (hP : 1 ≤ P)
    (hb : 2*P ≤ b) (hφ : b ≤ φ) (hd : 0 ≤ d) (hdφ : 4*d ≤ φ) :
    -4*d/φ ≤ Real.log (((φ-1-d)/(m+1))/((b-P)/(m+P))) := by
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hbP : 0 < b-P := by linarith only [hb,hPpos]
  have hφpos : 0 < φ := by linarith only [hPpos,hb,hφ]
  have hφP : 0 < φ-P := by linarith only [hPpos,hb,hφ]
  have hm1 : 0 < m+1 := by linarith only [hm]
  have hmP : 0 < m+P := by linarith only [hm,hPpos]
  let old := (b-P)/(m+P)
  let x := 1-d/(φ-P)
  have hold : 0 < old := div_pos hbP hmP
  have hfrac : d/(φ-P) ≤ 1/2 := (div_le_iff₀ hφP).mpr (by linarith only [hdφ,hb,hφ])
  have hxhalf : 1/2 ≤ x := by dsimp [x]; linarith only [hfrac]
  have hxpos : 0 < x := by linarith only [hxhalf]
  have hden : m+1 ≤ m+P := by linarith only [hP]
  have holdle : old ≤ (φ-P)/(m+1) := by
    dsimp [old]
    exact (div_le_div_of_nonneg_left hbP.le hm1 hden).trans
      (div_le_div_of_nonneg_right (by linarith only [hφ] : b-P ≤ φ-P) hm1.le)
  have hscaled := mul_le_mul_of_nonneg_left holdle hxpos.le
  have hcancel : x*((φ-P)/(m+1)) = (φ-P-d)/(m+1) := by
    dsimp [x]
    field_simp [hφP.ne',hm1.ne'] <;> ring
  rw [hcancel] at hscaled
  have hnew : (φ-P-d)/(m+1) ≤ (φ-1-d)/(m+1) :=
    div_le_div_of_nonneg_right (by linarith only [hP]) hm1.le
  have hratio : x ≤ ((φ-1-d)/(m+1))/old := (le_div_iff₀ hold).mpr (hscaled.trans hnew)
  have hlogmono := Real.log_le_log hxpos hratio
  have hlogabs := abs_log_le_twice_deviation hxhalf
  have hxabs : |x-1| = d/(φ-P) := by
    rw [show x-1 = -(d/(φ-P)) by dsimp [x]; ring,abs_neg,abs_of_nonneg (div_nonneg hd hφP.le)]
  rw [hxabs] at hlogabs
  have hfrac2 : d/(φ-P) ≤ 2*d/φ := by
    apply (div_le_div_iff₀ hφP hφpos).mpr
    have hh := mul_nonneg hd (show 0 ≤ φ-2*P by linarith only [hb,hφ])
    nlinarith only [hh]
  have hlo := (abs_le.mp hlogabs).1
  change -4*d/φ ≤ Real.log (((φ-1-d)/(m+1))/old)
  have hprice : -4*d/φ ≤ -(2*(d/(φ-P))) := by
    calc
      _ = -2*(2*d/φ) := by ring
      _ ≤ -2*(d/(φ-P)) := mul_le_mul_of_nonpos_left hfrac2 (by norm_num)
      _ = _ := by ring
  exact hprice.trans (hlo.trans hlogmono)

end
end StrongSilver
