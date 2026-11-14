-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PlanarConstruction
import StrongSilver.PowerNormalization

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 1000000

theorem eventually_working_head_geometry : ∀ᶠ A : ℝ in atTop,
    ∀ μ : ℝ, ∀ C : PlanarBoundaryCertificate A μ, ∀ P : ℝ,
      A^((49 : ℝ)/50) ≤ P → planarRadius A 0 ≤ 1+600/Real.log A ∧
        C.right+C.J 0 ≤ (600/Real.log A)*P := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),eventually_log_le_small_power,eventually_planar_head_radius,
    eventually_const_mul_negative_power_le_inverse_log (by norm_num : -(12 : ℝ)/25 < 0) (35 : ℝ)]
    with A hA hlog hr hsmall
  intro μ C P hP
  have hA0 : 0 < A := zero_lt_one.trans hA
  have hP0 : 0 ≤ P := (Real.rpow_pos_of_pos hA0 _).le.trans hP
  have hhead := C.head_size_bound hlog
  have hPmul := mul_le_mul_of_nonneg_left hP
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 35) (Real.rpow_pos_of_pos hA0 (-(12 : ℝ)/25)).le)
  have hp : A^(-(12 : ℝ)/25)*A^((49 : ℝ)/50) = A^((1 : ℝ)/2) := by
    rw [← Real.rpow_add hA0]
    congr 1
    norm_num
  have he : (35*A^(-(12 : ℝ)/25))*A^((49 : ℝ)/50) = 35*A^((1 : ℝ)/2) := by rw [← hp]; ring
  rw [he] at hPmul
  have hs := mul_le_mul_of_nonneg_right hsmall hP0
  have hlog0 := Real.log_pos hA
  have hlarge : 1/Real.log A ≤ 600/Real.log A := by
    apply div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 600) hlog0.le
  have hlast := mul_le_mul_of_nonneg_right hlarge hP0
  exact ⟨hr,hhead.trans (hPmul.trans (hs.trans hlast))⟩

end
end StrongSilver
