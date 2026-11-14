-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PlanarRiccatiSolution
import Mathlib.Analysis.Real.Pi.Bounds

namespace StrongSilver
open Real Set
noncomputable section

def planarEpsilon (A : ℝ) : ℝ := A^(-(1 : ℝ)/5)
def planarSlopeScale (A : ℝ) : ℝ := 100/Real.log A
def planarTerminalAngle (A : ℝ) : ℝ := Real.arctan (planarEpsilon A)⁻¹
def planarTerminalRadius (A : ℝ) : ℝ := Real.sqrt (1+(planarEpsilon A)^2)

theorem comparisonBound_elementary {ε k₀ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hk : 0 < k₀) (hk1 : k₀ ≤ 1/16) :
    planarComparisonBound (Real.arctan ε⁻¹) (Real.sqrt (1+ε^2)) k₀ ≤
      8*Real.exp (Real.arctan ε⁻¹/k₀)*(1+ε⁻¹^2) := by
  let Θ := Real.arctan ε⁻¹
  have hΘ0 : 0 ≤ Θ := (Real.arctan_pos.mpr (inv_pos.mpr hε)).le
  have hΘ2 : Θ ≤ 2 := by have hh := Real.arctan_lt_pi_div_two ε⁻¹; dsimp [Θ]; linarith [Real.pi_lt_four]
  have hR : Real.sqrt (1+ε^2) ≤ 2 := by
    have hh := Real.sq_sqrt (show 0 ≤ 1+ε^2 by positivity)
    have hs := Real.sqrt_nonneg (1+ε^2)
    nlinarith only [hh,hs,sq_nonneg (1-ε),hε1,hε]
  have hlog := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  have hcoef : k₀*Θ ≤ Real.log 2 := by
    have hm := mul_le_mul hk1 hΘ2 hΘ0 (by norm_num : (0 : ℝ) ≤ 1/16)
    norm_num at hlog
    linarith
  have he : Real.exp (k₀*Θ) ≤ 2 := by
    have hh := Real.exp_le_exp.mpr hcoef
    rwa [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hh
  have hprod : Real.sqrt (1+ε^2)*Real.exp (k₀*Θ)*Θ ≤ 8 := by
    have h12 := mul_le_mul hR he (Real.exp_pos _).le (by norm_num : (0 : ℝ) ≤ 2)
    have h123 := mul_le_mul h12 hΘ2 hΘ0 (by norm_num : (0 : ℝ) ≤ 2*2)
    norm_num at h123
    exact h123
  unfold planarComparisonBound
  rw [exp_inverseSlopePrimitive_terminal]
  have hlast : 0 ≤ Real.exp (Θ/k₀)*(1+ε⁻¹^2) := by positivity
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hprod hlast

theorem planarEpsilon_inverse_square {A : ℝ} (hA : 0 < A) : (planarEpsilon A)⁻¹^2 = A^((2 : ℝ)/5) := by
  unfold planarEpsilon
  rw [← Real.rpow_neg hA.le,← Real.rpow_mul_natCast hA.le]
  congr 1
  norm_num

theorem planarComparisonBound_power_bound {A : ℝ} (hA : 1 < A) (hlog : 1600 ≤ Real.log A) :
    planarComparisonBound (planarTerminalAngle A) (planarTerminalRadius A) (planarSlopeScale A) ≤
      16*A^((9 : ℝ)/20) := by
  have hApos : 0 < A := zero_lt_one.trans hA
  have hlogpos : 0 < Real.log A := Real.log_pos hA
  have hε : 0 < planarEpsilon A := Real.rpow_pos_of_pos hApos _
  have hε1 : planarEpsilon A ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hA.le (by norm_num)
  have hk : 0 < planarSlopeScale A := div_pos (by norm_num) hlogpos
  have hk1 : planarSlopeScale A ≤ 1/16 := (div_le_iff₀ hlogpos).mpr (by linarith)
  have hbase := comparisonBound_elementary hε hε1 hk hk1
  have hΘ2 : planarTerminalAngle A ≤ 2 := by
    have hh := Real.arctan_lt_pi_div_two (planarEpsilon A)⁻¹
    unfold planarTerminalAngle
    linarith [Real.pi_lt_four]
  have he : Real.exp (planarTerminalAngle A/planarSlopeScale A) ≤ A^((1 : ℝ)/20) := by
    rw [Real.rpow_def_of_pos hApos]
    apply Real.exp_le_exp.mpr
    unfold planarSlopeScale
    rw [div_div_eq_mul_div]
    nlinarith only [mul_le_mul_of_nonneg_right hΘ2 hlogpos.le,hlogpos]
  have hs : 1 ≤ A^((2 : ℝ)/5) := Real.one_le_rpow hA.le (by norm_num)
  have heps := planarEpsilon_inverse_square hApos
  change planarComparisonBound (planarTerminalAngle A) (planarTerminalRadius A) (planarSlopeScale A) ≤
    8*Real.exp (planarTerminalAngle A/planarSlopeScale A)*(1+(planarEpsilon A)⁻¹^2) at hbase
  rw [heps] at hbase
  have hmul := mul_le_mul he (show 1+A^((2 : ℝ)/5) ≤ 2*A^((2 : ℝ)/5) by linarith)
    (by positivity : 0 ≤ 1+A^((2 : ℝ)/5)) (Real.rpow_nonneg hApos.le _)
  have hadd : A^((1 : ℝ)/20)*A^((2 : ℝ)/5) = A^((9 : ℝ)/20) := by
    rw [← Real.rpow_add hApos]
    congr 1
    norm_num
  nlinarith only [hbase,hmul,hadd]

end
end StrongSilver
