-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.Constants
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 1800000

/-- A logarithm is uniformly absorbed by a positive power near zero. -/
theorem rpow_log_inverse_le {z q : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) (hq : 0 < q) :
    z^q*(-Real.log z) ≤ 1/q := by
  have hp := Real.rpow_pos_of_pos hz q
  have hh := Real.one_sub_inv_le_log_of_pos hp
  have hm := mul_le_mul_of_nonneg_left hh hp.le
  rw [Real.log_rpow hz] at hm
  have he : z^q*(1-(z^q)⁻¹) = z^q-1 := by field_simp
  rw [he] at hm
  apply (le_div_iff₀ hq).mpr
  nlinarith only [hm,hp]

/-- A reference cutoff separates log(kappa/B) into a fixed term and a
uniformly power-weighted logarithm of the relative cutoff. -/
theorem cutoff_rpow_log_bound {B cap κ q : ℝ} (hB : 0 < B) (hBcap : B ≤ cap)
    (hcapκ : cap ≤ κ) (hq : 0 < q) :
    (B/cap)^q*(1+Real.log (κ/B)) ≤ 1+Real.log (κ/cap)+1/q := by
  have hcap := hB.trans_le hBcap
  have hκ := hcap.trans_le hcapκ
  have hz := div_pos hB hcap
  have hz1 := (div_le_one hcap).mpr hBcap
  have hpower := Real.rpow_le_rpow hz.le hz1 hq.le
  simp only [Real.one_rpow] at hpower
  have hlog := Real.log_nonneg ((one_le_div hcap).mpr hcapκ)
  have hm := mul_le_mul_of_nonneg_right hpower (by linarith only [hlog] : 0 ≤ 1+Real.log (κ/cap))
  have hd := rpow_log_inverse_le hz hz1 hq
  have he : Real.log (κ/B) = Real.log (κ/cap)-Real.log (B/cap) := by
    rw [Real.log_div hκ.ne' hB.ne',Real.log_div hκ.ne' hcap.ne',Real.log_div hB.ne' hcap.ne']
    ring
  rw [he]
  nlinarith only [hm,hd]

end
end StrongSilver
