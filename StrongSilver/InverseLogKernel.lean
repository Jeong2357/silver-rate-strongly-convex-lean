-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.QuadraticLogs
import Mathlib.MeasureTheory.Integral.Average

namespace StrongSilver
open Set MeasureTheory Real
noncomputable section

def inverseLogKernel (t : ℝ) : ℝ := (Icc (-1 : ℝ) 1).indicator (fun x => -Real.log x) t

theorem inverseLogKernel_eq (t : ℝ) : inverseLogKernel t = max 0 (-Real.log t) := by
  by_cases ht : t ∈ Icc (-1 : ℝ) 1
  · have habs : |t| ≤ 1 := abs_le.mpr ht
    have hl : Real.log t ≤ 0 := by
      rw [← Real.log_abs]
      exact Real.log_nonpos (abs_nonneg _) habs
    simp only [inverseLogKernel,indicator_of_mem ht,max_eq_right (by linarith : 0 ≤ -Real.log t)]
  · have habs : 1 ≤ |t| := by
      by_contra hh
      exact ht (abs_le.mp (le_of_lt (lt_of_not_ge hh)))
    have hl : 0 ≤ Real.log t := by
      rw [← Real.log_abs]
      exact Real.log_nonneg habs
    simp only [inverseLogKernel,indicator_of_notMem ht,max_eq_left (by linarith : -Real.log t ≤ 0)]

theorem inverseLogKernel_nonneg (t : ℝ) : 0 ≤ inverseLogKernel t := by
  rw [inverseLogKernel_eq]
  exact le_max_left _ _

theorem inverseLogKernel_integrable : Integrable inverseLogKernel volume := by
  have hi : IntegrableOn (fun x : ℝ => -Real.log x) (Icc (-1 : ℝ) 1) volume := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (-1 : ℝ) ≤ 1)).mp
    exact (intervalIntegral.intervalIntegrable_log' (a := (-1 : ℝ)) (b := 1)).neg
  exact hi.integrable_indicator measurableSet_Icc

theorem inverseLogKernel_integral : (∫ t : ℝ, inverseLogKernel t) = 2 := by
  unfold inverseLogKernel
  rw [integral_indicator measurableSet_Icc,integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),intervalIntegral.integral_neg,
    integral_log]
  norm_num

theorem inverseLogKernel_interval_bound {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b, inverseLogKernel t) ≤ 2 := by
  rw [intervalIntegral.integral_of_le hab,← inverseLogKernel_integral]
  exact setIntegral_le_integral inverseLogKernel_integrable (Filter.Eventually.of_forall inverseLogKernel_nonneg)

theorem inverseLogKernel_affine_integrable (x a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => inverseLogKernel (1-x*t)) volume a b := by
  simp_rw [inverseLogKernel_eq]
  exact ⟨integrable_const (0 : ℝ) |>.sup (quadratic_log_integrable x a b).1.neg,
    integrable_const (0 : ℝ) |>.sup (quadratic_log_integrable x a b).2.neg⟩

theorem inverseLogKernel_affine_bound {x a b : ℝ} (hx : 0 < x) (hab : a ≤ b) :
    (∫ t in a..b, inverseLogKernel (1-x*t)) ≤ 2/x := by
  rw [intervalIntegral.integral_comp_sub_mul inverseLogKernel hx.ne' 1]
  simp only [smul_eq_mul]
  have hh := inverseLogKernel_interval_bound (show 1-x*b ≤ 1-x*a by nlinarith)
  have hm := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hx.le)
  simpa only [div_eq_mul_inv,mul_comm] using hm

end
end StrongSilver
