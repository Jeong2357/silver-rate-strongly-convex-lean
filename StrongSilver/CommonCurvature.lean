-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.InverseLogKernel
import StrongSilver.ScalarQuadraticAverage
import StrongSilver.WeightedCount

namespace StrongSilver
open Set MeasureTheory Filter
noncomputable section

def largeInverseCharge (κ : ℝ) (h : List ℝ) (μ : ℝ) : ℝ :=
  (h.map (fun b => if κ/2 < b then inverseLogKernel (1-μ*b) else 0)).sum

theorem largeInverseCharge_integrable (κ : ℝ) (h : List ℝ) :
    IntervalIntegrable (fun t : ℝ => largeInverseCharge κ h (t/κ)) volume 1 (9/8) := by
  induction h with
  | nil => exact intervalIntegrable_const
  | cons b h ih =>
    change IntervalIntegrable (fun t : ℝ =>
      (if κ/2 < b then inverseLogKernel (1-(t/κ)*b) else 0)+largeInverseCharge κ h (t/κ)) volume 1 (9/8)
    apply IntervalIntegrable.add _ ih
    by_cases hb : κ/2 < b
    · simp only [hb,if_true]
      convert! inverseLogKernel_affine_integrable (b/κ) 1 (9/8) using 1
      ext t
      congr 2
      ring
    · simp only [hb,if_false]
      exact intervalIntegrable_const

theorem largeInverseCharge_integral_bound {κ : ℝ} (hκ : 0 < κ) (h : List ℝ) :
    (∫ t in (1 : ℝ)..(9/8), largeInverseCharge κ h (t/κ)) ≤
      4*(countAbove h (κ/2) : ℝ) := by
  induction h with
  | nil => simp [largeInverseCharge]
  | cons b h ih =>
    have hi : IntervalIntegrable (fun t : ℝ => if κ/2 < b then inverseLogKernel (1-(t/κ)*b) else 0)
        volume 1 (9/8) := by
      by_cases hb : κ/2 < b
      · simp only [hb,if_true]
        convert! inverseLogKernel_affine_integrable (b/κ) 1 (9/8) using 1
        ext t
        congr 2
        ring
      · simp only [hb,if_false]
        exact intervalIntegrable_const
    change (∫ t in (1 : ℝ)..(9/8),
      (if κ/2 < b then inverseLogKernel (1-(t/κ)*b) else 0)+largeInverseCharge κ h (t/κ)) ≤ _
    rw [intervalIntegral.integral_add hi (largeInverseCharge_integrable κ h),countAbove_cons,Nat.cast_add]
    by_cases hb : κ/2 < b
    · have hx : 1/2 < b/κ := (lt_div_iff₀ hκ).mpr (by linarith)
      have he : (∫ t in (1 : ℝ)..(9/8), inverseLogKernel (1-(t/κ)*b)) =
          ∫ t in (1 : ℝ)..(9/8), inverseLogKernel (1-(b/κ)*t) := by
        congr 1
        ext t
        congr 2
        ring
      simp only [hb,hb.le,if_true,Nat.cast_one]
      rw [he]
      have hI := inverseLogKernel_affine_bound (lt_trans (by norm_num) hx) (by norm_num : (1 : ℝ) ≤ 9/8)
      have hfour : 2/(b/κ) ≤ 4 := (div_le_iff₀ (lt_trans (by norm_num) hx)).mpr (by linarith)
      linarith
    · simp only [hb,if_false,intervalIntegral.integral_zero]
      by_cases hb' : κ/2 ≤ b <;> simp only [hb',if_true,if_false,Nat.cast_one,Nat.cast_zero] <;> linarith

/-- A single auxiliary curvature avoids every root and controls all large-step inverse factors. -/
theorem exists_common_curvature {κ : ℝ} (hκ : 0 < κ) (h : List ℝ) :
    ∃ μ : ℝ, 1/κ ≤ μ ∧ μ ≤ 9/(8*κ) ∧ (∀ b ∈ h, 1-μ*b ≠ 0) ∧
      largeInverseCharge κ h μ ≤ 32*(countAbove h (κ/2) : ℝ) := by
  let S := Icc (1 : ℝ) (9/8)
  let f : ℝ → ℝ := fun t => largeInverseCharge κ h (t/κ)
  have hi : IntegrableOn f S volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (1 : ℝ) ≤ 9/8)).mp
      (largeInverseCharge_integrable κ h)
  have hmean : (⨍ t in S, f t) ≤ 32*(countAbove h (κ/2) : ℝ) := by
    rw [setAverage_eq]
    have hreal : volume.real S = (1 : ℝ)/8 := by norm_num [S,measureReal_def,Real.volume_Icc]
    rw [hreal]
    change ((1 : ℝ)/8)⁻¹ • (∫ t in Icc (1 : ℝ) (9/8), f t) ≤ _
    rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 9/8)]
    simp only [smul_eq_mul]
    norm_num
    have hI := largeInverseCharge_integral_bound hκ h
    change (∫ t in (1 : ℝ)..(9/8), f t) ≤ _ at hI
    linarith
  let N : Set ℝ := {t | ¬ (∀ b ∈ h, 1-(t/κ)*b ≠ 0)}
  have hN : volume N = 0 := by
    exact (ae_iff).mp (step_factors_ae_nonzero h κ)
  have hspos : 0 < volume {t ∈ S | f t ≤ ⨍ a in S, f a} :=
    measure_le_setAverage_pos (by norm_num [S,Real.volume_Icc])
      (by simp [S,Real.volume_Icc]) hi
  rw [← measure_sdiff_null hN] at hspos
  obtain ⟨t,ht,hnt⟩ := nonempty_of_measure_ne_zero hspos.ne'
  have htS : t ∈ S := ht.1
  have hft : f t ≤ ⨍ a in S, f a := ht.2
  have hn : ∀ b ∈ h, 1-(t/κ)*b ≠ 0 := by simpa only [N,mem_setOf_eq,not_not] using hnt
  refine ⟨t/κ,(div_le_div_iff_of_pos_right hκ).mpr htS.1,?_,hn,hft.trans hmean⟩
  have he : 9/(8*κ) = (9/8)/κ := by ring
  rw [he]
  exact (div_le_div_iff_of_pos_right hκ).mpr htS.2

end
end StrongSilver
