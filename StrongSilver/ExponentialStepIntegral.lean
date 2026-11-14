-- SPDX-License-Identifier: GPL-3.0-only
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace StrongSilver
open Real Set MeasureTheory
noncomputable section
set_option maxHeartbeats 2800000

theorem scaled_exponential_integral (v a b : ℝ) :
    v*(∫ y in a..b, Real.exp (v*y)) = Real.exp (v*b)-Real.exp (v*a) := by
  have hh := intervalIntegral.smul_integral_comp_mul_left Real.exp v (a := a) (b := b)
  simpa only [smul_eq_mul,integral_exp] using hh

theorem exponential_step_intervalIntegrable (v c a b : ℝ) :
    IntervalIntegrable (fun y => if y < c then Real.exp (v*y) else 0) volume a b := by
  have hcont : Continuous (fun y : ℝ => Real.exp (v*y)) := Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hexp : IntervalIntegrable (fun y : ℝ => Real.exp (v*y)) volume a b := hcont.intervalIntegrable a b
  have hm : Measurable (fun y : ℝ => if y < c then Real.exp (v*y) else 0) :=
    Measurable.ite measurableSet_Iio hcont.measurable measurable_const
  apply hexp.mono_fun' hm.aestronglyMeasurable.restrict
  filter_upwards [] with y
  by_cases hy : y < c
  · simp only [if_pos hy,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact le_rfl
  · simp only [if_neg hy,norm_zero]
    exact (Real.exp_pos _).le

/-- The weighted integral of one finite jump, valid also when its
height equals an endpoint. -/
theorem exponential_step_integral (v a b c : ℝ) (hab : a ≤ b) :
    v*(∫ y in a..b, if y < c then Real.exp (v*y) else 0) =
      Real.exp (v*min b c)-Real.exp (v*min a c) := by
  by_cases hca : c ≤ a
  · have he : (∫ y in a..b, if y < c then Real.exp (v*y) else 0) = 0 := by
      calc
        _ = ∫ y in a..b, (0:ℝ) := by
          apply intervalIntegral.integral_congr_Ioo_of_le hab
          intro y hy
          exact if_neg (not_lt_of_ge (hca.trans hy.1.le))
        _ = 0 := intervalIntegral.integral_zero
    rw [he,mul_zero,min_eq_right (hca.trans hab),min_eq_right hca,sub_self]
  · by_cases hbc : b ≤ c
    · have he : (∫ y in a..b, if y < c then Real.exp (v*y) else 0) = ∫ y in a..b, Real.exp (v*y) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hab
        intro y hy
        exact if_pos (hy.2.trans_le hbc)
      rw [he,min_eq_left hbc,min_eq_left (hab.trans hbc),scaled_exponential_integral]
    · have hac : a ≤ c := (le_of_not_ge hca)
      have hcb : c ≤ b := (le_of_not_ge hbc)
      have he : (∫ y in a..b, if y < c then Real.exp (v*y) else 0) =
          ∫ y in a..b, indicator {x : ℝ | x ≤ c} (fun y => Real.exp (v*y)) y := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [volume.ae_ne c] with y hy
        intro _
        simp only [indicator_apply,mem_setOf_eq]
        have hiff : y < c ↔ y ≤ c := ⟨le_of_lt,fun h => lt_of_le_of_ne h hy⟩
        simp only [hiff]
      rw [he,intervalIntegral.integral_indicator ⟨hac,hcb⟩,scaled_exponential_integral,
        min_eq_right hcb,min_eq_left hac]

end
end StrongSilver
