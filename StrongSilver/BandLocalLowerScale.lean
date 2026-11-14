-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandLocalScaleBounds

namespace StrongSilver
open Real
noncomputable section
set_option maxHeartbeats 4400000

theorem bandLocalLowerDenominator_root_product : bandLocalLowerDenominator*bandRootScaleConstant = 25000 := by
  unfold bandLocalLowerDenominator bandRootScaleConstant
  rw [Real.exp_neg]
  field_simp [Real.exp_ne_zero (3:ℝ)] <;> ring

/-- The concrete common lower scale fits inside every depth group and
is much smaller than the following gap's actual positive root step. -/
theorem band_local_lower_scale_bounds (u A M b : ℝ) (hA : 0 < A)
    (hM : bandRootScaleConstant*A ≤ M) (hb : bandRootScaleConstant*A ≤ b) :
    0 < bandLocalLowerScale u A ∧
      bandLocalLowerScale u A ≤ (1/4:ℝ)^(fourPhaseDepth u+2)*M ∧ 64*bandLocalLowerScale u A ≤ b := by
  let K := bandLocalLowerDenominator
  let D := (4:ℝ)^(fourPhaseDepth u+2)
  have hK : 0 < K := bandLocalLowerDenominator_positive
  have hD : 0 < D := pow_pos (by norm_num) _
  have hKD : 0 < K*D := mul_pos hK hD
  have hProduct : (bandRootScaleConstant*A)*K = 25000*A := by
    calc
      _ = (bandLocalLowerDenominator*bandRootScaleConstant)*A := by dsimp only [K]; ring
      _ = _ := by rw [bandLocalLowerDenominator_root_product]
  have hSmall : A/K ≤ bandRootScaleConstant*A := by
    apply (div_le_iff₀ hK).mpr
    rw [hProduct]
    linarith only [hA]
  have hFour : 4*A/K ≤ bandRootScaleConstant*A := by
    apply (div_le_iff₀ hK).mpr
    rw [hProduct]
    linarith only [hA]
  have hPow : (1:ℝ) ≤ (4:ℝ)^fourPhaseDepth u := one_le_pow₀ (by norm_num)
  have hD16 : (16:ℝ) ≤ D := by
    dsimp only [D]
    rw [pow_add]
    norm_num
    linarith only [hPow]
  have hD16K := mul_le_mul_of_nonneg_left hD16 hK.le
  have hL16 : bandLocalLowerScale u A ≤ A/(16*K) := by
    have hh := div_le_div_of_nonneg_left hA.le (mul_pos (by norm_num : (0:ℝ) < 16) hK)
      (show 16*K ≤ K*D by linear_combination hD16K)
    exact hh
  have hMdepth : bandLocalLowerScale u A ≤ (1/4:ℝ)^(fourPhaseDepth u+2)*M := by
    calc
      _ = (A/K)/D := by dsimp only [bandLocalLowerScale,K,D]; ring
      _ ≤ M/D := div_le_div_of_nonneg_right (hSmall.trans hM) hD.le
      _ = _ := by rw [one_div_pow]; dsimp only [D]; ring
  have hRight : 64*bandLocalLowerScale u A ≤ b := by
    have hS := mul_le_mul_of_nonneg_left hL16 (by norm_num : (0:ℝ) ≤ 64)
    have hEq : 64*(A/(16*K)) = 4*A/K := by ring
    rw [hEq] at hS
    exact hS.trans (hFour.trans hb)
  exact ⟨div_pos hA hKD,hMdepth,hRight⟩

end
end StrongSilver
