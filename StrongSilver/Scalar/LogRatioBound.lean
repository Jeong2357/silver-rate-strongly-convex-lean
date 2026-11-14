-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.Scalar.SilverConstants

namespace StrongSilver.Scalar.Calculus
noncomputable section
set_option maxHeartbeats 800000

theorem log_ratio_bound (a r : ℝ) (hr : 0 < r) (ha : r/2 ≤ a) :
    |Real.log (a/r)| ≤ (2/r)*|a-r| := by
  have ha0 : 0 < a := lt_of_lt_of_le (by linarith) ha
  have hr2 : 0 < r/2 := by linarith
  have hlog := Real.log_le_sub_one_of_pos (div_pos ha0 hr)
  have hlogInv := Real.log_le_sub_one_of_pos (inv_pos.mpr (div_pos ha0 hr))
  rw [Real.log_inv,inv_div] at hlogInv
  have hu : Real.log (a/r) ≤ (2/r)*|a-r| := by
    calc
      _ ≤ (a-r)/r := by linarith [show a/r-1=(a-r)/r by field_simp [hr.ne'] <;> ring]
      _ ≤ |a-r|/r := div_le_div_of_nonneg_right (le_abs_self _) hr.le
      _ ≤ (2/r)*|a-r| := by
        rw [show (2/r)*|a-r|=2*(|a-r|/r) by ring]
        have h := div_nonneg (abs_nonneg (a-r)) hr.le
        linarith
  have hl : -Real.log (a/r) ≤ (2/r)*|a-r| := by
    calc
      _ ≤ (r-a)/a := by linarith [show r/a-1=(r-a)/a by field_simp [ha0.ne'] <;> ring]
      _ ≤ |a-r|/a := div_le_div_of_nonneg_right (by have h := neg_le_abs (a-r); linarith) ha0.le
      _ ≤ |a-r|/(r/2) := div_le_div_of_nonneg_left (abs_nonneg _) hr2 ha
      _ = (2/r)*|a-r| := by field_simp <;> ring
  exact abs_le.mpr ⟨by linarith,hu⟩

theorem log_ratio_sq_bound (a r : ℝ) (hr : 0 < r) (ha : r/2 ≤ a) :
    (Real.log (a/r))^2 ≤ (2/r)^2*(a-r)^2 := by
  have h := log_ratio_bound a r hr ha
  have hM : 0 ≤ (2/r)*|a-r| := mul_nonneg (by positivity) (abs_nonneg _)
  have hs := mul_nonneg (sub_nonneg.mpr h) (add_nonneg hM (abs_nonneg (Real.log (a/r))))
  have hsq : |Real.log (a/r)|^2 ≤ ((2/r)*|a-r|)^2 := by nlinarith
  simpa only [sq_abs,mul_pow] using hsq

end
end StrongSilver.Scalar.Calculus
