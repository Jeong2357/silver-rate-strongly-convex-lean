-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PowerMargins

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 1800000

theorem initial_band_pad_bounds {B A ξ : ℝ} (hB : 1 ≤ B) (hξ : 0 ≤ ξ) (hξmax : ξ ≤ 1/1000)
    (hA : B^(1-ξ) ≤ A) (hAB : A ≤ B) :
    A^((49 : ℝ)/50) ≤ B^((987 : ℝ)/1000) ∧ B^((987 : ℝ)/1000) ≤ A^((199 : ℝ)/200) := by
  have hB0 := zero_lt_one.trans_le hB
  have hfloor := Real.one_le_rpow hB (show 0 ≤ 1-ξ by linarith only [hξmax])
  have hA0 := zero_lt_one.trans_le (hfloor.trans hA)
  constructor
  · exact (Real.rpow_le_rpow hA0.le hAB (by norm_num : (0 : ℝ) ≤ 49/50)).trans
      (Real.rpow_le_rpow_of_exponent_le hB (by norm_num : (49 : ℝ)/50 ≤ 987/1000))
  · calc
      _ ≤ B^((1-ξ)*((199 : ℝ)/200)) := Real.rpow_le_rpow_of_exponent_le hB (by linarith only [hξmax])
      _ = (B^(1-ξ))^((199 : ℝ)/200) := Real.rpow_mul hB0.le _ _
      _ ≤ _ := Real.rpow_le_rpow (Real.rpow_pos_of_pos hB0 _).le hA (by norm_num)

theorem eventually_initial_band_pad_margin {ξ : ℝ} (hξ : ξ ≤ 1/1000) :
    ∀ᶠ B : ℝ in atTop, 2*B^((987 : ℝ)/1000) ≤ B^(1-ξ) :=
  eventually_const_mul_power_le (by linarith only [hξ] : (987 : ℝ)/1000 < 1-ξ) 2

theorem initial_band_log_bounds {B A ξ : ℝ} (hB : 0 < B) (hA : 0 < A)
    (hfloor : B^(1-ξ) ≤ A) : (1-ξ)*Real.log B ≤ Real.log A ∧ Real.log (B/A) ≤ ξ*Real.log B := by
  have hh := Real.log_le_log (Real.rpow_pos_of_pos hB (1-ξ)) hfloor
  rw [Real.log_rpow hB] at hh
  refine ⟨hh,?_⟩
  rw [Real.log_div hB.ne' hA.ne']
  linarith only [hh]

theorem near_cutoff_root_bound {B κ ε : ℝ} (hB : 0 < B) (hκ : 0 < κ) (hε : ε < 1)
    (hnear : κ^(1-ε) ≤ B) : κ ≤ B^(1/(1-ε)) := by
  have hd : 0 < 1-ε := sub_pos.mpr hε
  have hh := Real.rpow_le_rpow (Real.rpow_pos_of_pos hκ (1-ε)).le hnear (one_div_nonneg.mpr hd.le)
  rw [← Real.rpow_mul hκ.le,show (1-ε)*(1/(1-ε)) = (1 : ℝ) by field_simp,Real.rpow_one] at hh
  exact hh

theorem near_initial_band_kappa_bound {B A κ ε ξ : ℝ} (hB : 1 ≤ B) (hκ : 0 < κ) (hε : ε < 1)
    (hnear : κ^(1-ε) ≤ B) (hfloor : B^(1-ξ) ≤ A)
    (hscale : 1 ≤ (1-ε)*(1-ξ)*((1003 : ℝ)/1000)) : κ ≤ A^((1003 : ℝ)/1000) := by
  have hB0 := zero_lt_one.trans_le hB
  have hroot := near_cutoff_root_bound hB0 hκ hε hnear
  have hd : 0 < 1-ε := sub_pos.mpr hε
  have hexp : 1/(1-ε) ≤ (1-ξ)*((1003 : ℝ)/1000) := (div_le_iff₀ hd).mpr (by nlinarith only [hscale])
  calc
    _ ≤ B^(1/(1-ε)) := hroot
    _ ≤ B^((1-ξ)*((1003 : ℝ)/1000)) := Real.rpow_le_rpow_of_exponent_le hB hexp
    _ = (B^(1-ξ))^((1003 : ℝ)/1000) := Real.rpow_mul hB0.le _ _
    _ ≤ _ := Real.rpow_le_rpow (Real.rpow_pos_of_pos hB0 _).le hfloor (by norm_num)

end
end StrongSilver
