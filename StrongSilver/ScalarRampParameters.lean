-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ScalarRamp

namespace StrongSilver
open Real
noncomputable section
set_option maxHeartbeats 1000000

theorem exists_selected_scalar_ramp {b T e : ℝ} (hb : 8 ≤ b) (hbT : b < T) (he : 0 < e) :
    ∃ R : ScalarRamp, R.base = 1/T ∧ R.amplitude = (1/b-1/T)*e ∧
      e/2 ≤ R.threshold ∧ R.threshold ≤ e ∧ R.physical e = e/b := by
  have hb0 : 0 < b := by linarith
  have hT0 : 0 < T := hb0.trans hbT
  let s : ℝ := 1/T
  let a : ℝ := (1/b-s)*e
  let δ : ℝ := 1/2-s
  let v : ℝ := e-a/δ
  have hs0 : 0 < s := one_div_pos.mpr hT0
  have hsb : s < 1/b := by dsimp [s]; exact one_div_lt_one_div_of_lt hb0 hbT
  have hble : 1/b ≤ 1/8 := (one_div_le_one_div hb0 (show (0 : ℝ) < 8 by norm_num)).mpr hb
  have hs8 : s ≤ 1/8 := hsb.le.trans hble
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have ha : 0 < a := mul_pos (sub_pos.mpr hsb) he
  have hhalf : a/δ ≤ e/2 := by
    apply (div_le_iff₀ hδ).mpr
    dsimp [a,δ]
    have hm := mul_le_mul_of_nonneg_right hble he.le
    have hs := mul_nonneg hs0.le he.le
    nlinarith only [hm,hs,he]
  have hvhalf : e/2 ≤ v := by dsimp [v]; linarith only [hhalf]
  have hv0 : 0 ≤ v := (by linarith : 0 ≤ e/2).trans hvhalf
  have hve : v ≤ e := by dsimp [v]; exact sub_le_self _ (div_nonneg ha.le hδ.le)
  let R : ScalarRamp := {
    base := s
    threshold := v
    amplitude := a
    base_nonnegative := hs0.le
    base_le_half := by linarith
    threshold_nonnegative := hv0
    amplitude_nonnegative := ha.le
  }
  refine ⟨R,rfl,rfl,hvhalf,hve,?_⟩
  have hsoft : softThreshold v e = e-v := by
    rw [softThreshold_of_nonnegative hv0 he.le,max_eq_left (sub_nonneg.mpr hve)]
  have hcap : δ*(e-v) = a := by
    dsimp [v]
    field_simp [hδ.ne']
    <;> ring
  change s*e+symmetricClip a (δ*softThreshold v e) = e/b
  rw [hsoft,hcap,symmetricClip_of_nonnegative ha.le ha.le,min_self]
  dsimp [a,s]
  ring

theorem scalar_ramp_selected_step {R : ScalarRamp} {b e : ℝ} (hselected : R.physical e = e/b) (hb : b ≠ 0) :
    e-b*R.physical e = 0 := by rw [hselected,mul_div_cancel₀ e hb,sub_self]

end
end StrongSilver
