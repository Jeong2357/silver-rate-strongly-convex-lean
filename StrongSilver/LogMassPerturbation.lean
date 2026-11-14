-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.Constants
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 2600000

/-- A logarithmic mass change is bounded by its absolute change divided
by a common positive lower scale. -/
theorem log_mass_perturbation {x y scale error : ℝ} (hs : 0 < scale)
    (hx : scale ≤ x) (hy : scale ≤ y) (he : 0 ≤ error) (hd : |x-y| ≤ error) :
    |Real.log x-Real.log y| ≤ error/scale := by
  have hx0 := hs.trans_le hx
  have hy0 := hs.trans_le hy
  have hxy := Real.log_le_sub_one_of_pos (div_pos hx0 hy0)
  have hyx := Real.log_le_sub_one_of_pos (div_pos hy0 hx0)
  rw [Real.log_div hx0.ne' hy0.ne'] at hxy
  rw [Real.log_div hy0.ne' hx0.ne'] at hyx
  have hdiff := abs_le.mp hd
  have hUpper : x/y-1 ≤ error/scale := by
    rw [div_sub_one hy0.ne']
    apply (div_le_iff₀ hy0).mpr
    have hh := mul_le_mul_of_nonneg_left hy (div_nonneg he hs.le)
    have hid : error/scale*scale = error := by field_simp
    rw [hid] at hh
    linarith only [hdiff.2,hh]
  have hLower : y/x-1 ≤ error/scale := by
    rw [div_sub_one hx0.ne']
    apply (div_le_iff₀ hx0).mpr
    have hh := mul_le_mul_of_nonneg_left hx (div_nonneg he hs.le)
    have hid : error/scale*scale = error := by field_simp
    rw [hid] at hh
    linarith only [hdiff.1,hh]
  apply abs_le.mpr
  constructor <;> linarith only [hxy,hyx,hUpper,hLower]

end
end StrongSilver
