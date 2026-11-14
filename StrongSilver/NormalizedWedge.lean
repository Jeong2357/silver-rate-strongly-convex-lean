-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.WedgeGeometry

namespace StrongSilver
open Real
noncomputable section
set_option maxHeartbeats 1000000

def normalizedWedgeCos (γ : ℝ) : ℝ := (Real.sqrt (1+γ^2))⁻¹
def normalizedWedgeSin (γ : ℝ) : ℝ := γ*normalizedWedgeCos γ

theorem normalizedWedge_properties {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    0 < normalizedWedgeCos γ ∧ 0 < normalizedWedgeSin γ ∧ normalizedWedgeSin γ ≤ normalizedWedgeCos γ ∧
    (normalizedWedgeCos γ)^2+(normalizedWedgeSin γ)^2 = 1 ∧
    1/2 ≤ normalizedWedgeCos γ ∧ normalizedWedgeCos γ ≤ 1 ∧
    γ/2 ≤ normalizedWedgeSin γ ∧ normalizedWedgeSin γ ≤ γ := by
  have hroot : 0 < Real.sqrt (1+γ^2) := Real.sqrt_pos.mpr (by positivity)
  have hsqrt := Real.sq_sqrt (show 0 ≤ 1+γ^2 by positivity)
  have hroot1 : 1 ≤ Real.sqrt (1+γ^2) := by nlinarith only [hsqrt,hroot,sq_nonneg γ]
  have hroot2 : Real.sqrt (1+γ^2) ≤ 2 := by nlinarith only [hsqrt,hroot,hγ,hγ1]
  have hc : 0 < normalizedWedgeCos γ := inv_pos.mpr hroot
  have hcL : 1/2 ≤ normalizedWedgeCos γ := by
    simp only [normalizedWedgeCos, ← one_div]
    apply (le_div_iff₀ hroot).mpr
    linarith only [hroot2]
  have hcU : normalizedWedgeCos γ ≤ 1 := by
    simp only [normalizedWedgeCos, ← one_div]
    exact (div_le_one hroot).mpr hroot1
  have hs : 0 < normalizedWedgeSin γ := mul_pos hγ hc
  have hsc : normalizedWedgeSin γ ≤ normalizedWedgeCos γ := by
    have hh := mul_le_mul_of_nonneg_right hγ1 hc.le
    simpa only [normalizedWedgeSin,one_mul] using hh
  have hunit : (normalizedWedgeCos γ)^2+(normalizedWedgeSin γ)^2 = 1 := by
    unfold normalizedWedgeSin normalizedWedgeCos
    field_simp [hroot.ne']
    nlinarith only [hsqrt]
  have hsL : γ/2 ≤ normalizedWedgeSin γ := by
    have hh := mul_le_mul_of_nonneg_left hcL hγ.le
    dsimp [normalizedWedgeSin]
    nlinarith only [hh]
  have hsU : normalizedWedgeSin γ ≤ γ := by
    have hh := mul_le_mul_of_nonneg_left hcU hγ.le
    simpa only [normalizedWedgeSin,mul_one] using hh
  exact ⟨hc,hs,hsc,hunit,hcL,hcU,hsL,hsU⟩

theorem normalizedWedge_ratio {γ : ℝ} (hγ : 0 < γ) :
    normalizedWedgeCos γ/normalizedWedgeSin γ = 1/γ := by
  have hc : normalizedWedgeCos γ ≠ 0 := (inv_pos.mpr (Real.sqrt_pos.mpr (by positivity : 0 < 1+γ^2))).ne'
  unfold normalizedWedgeSin
  field_simp [hc,hγ.ne']

end
end StrongSilver
