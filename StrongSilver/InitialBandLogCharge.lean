-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.InitialThresholdBand

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 1600000

/-- The selected-count error is uniformly small on a short logarithmic
threshold band, after its exact weighted moment charge. -/
theorem initial_band_selected_log_charge {B A ξ : ℝ} (hB : 1 < B) (hξ : ξ < 1)
    (hfloor : B^(1-ξ) ≤ A) (hAB : A ≤ B) :
    (1200/Real.log A)*(1+Real.log (B/A)) ≤
      (1200/(1-ξ))*(1/Real.log B+ξ) := by
  have hB0 := zero_lt_one.trans hB
  have hd := sub_pos.mpr hξ
  have hfloor1 : 1 < B^(1-ξ) := Real.one_lt_rpow hB hd
  have hA1 := hfloor1.trans_le hfloor
  have hA0 := zero_lt_one.trans hA1
  obtain ⟨hlog,hgap⟩ := initial_band_log_bounds hB0 hA0 hfloor
  have hlogB := Real.log_pos hB
  have hlogA := Real.log_pos hA1
  have hlogRatio := Real.log_nonneg ((one_le_div hA0).mpr hAB)
  have hnum : 0 ≤ 1200*(1+ξ*Real.log B) := by linarith only [hgap,hlogRatio]
  calc
    _ = 1200*(1+Real.log (B/A))/Real.log A := by ring
    _ ≤ 1200*(1+ξ*Real.log B)/Real.log A := by gcongr
    _ ≤ 1200*(1+ξ*Real.log B)/((1-ξ)*Real.log B) :=
      div_le_div_of_nonneg_left hnum (mul_pos hd hlogB) hlog
    _ = _ := by field_simp <;> ring

end
end StrongSilver
