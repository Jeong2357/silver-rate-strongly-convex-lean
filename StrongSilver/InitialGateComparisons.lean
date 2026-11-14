-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.InitialOldGate
import StrongSilver.InitialConstantBounds

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 1800000

theorem eventually_initial_old_gate_small : ∀ᶠ A : ℝ in atTop,
    ∀ κ B : ℝ, 0 ≤ κ → κ ≤ A^((1003 : ℝ)/1000) → A ≤ B →
      initialOldGate A κ B ≤ A^(-(19 : ℝ)/100) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    eventually_const_mul_power_le (by norm_num : -(197 : ℝ)/1000 < -(19 : ℝ)/100) (2*initialOldGateConstant)]
    with A hA hmargin
  intro κ B hκ hκA hAB
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  have hB : 0 < B := hA0.trans_le hAB
  have h1 : A^(-(1 : ℝ)/5)*κ/B ≤ A^(-(197 : ℝ)/1000) := by
    calc
      _ ≤ A^(-(1 : ℝ)/5)*A^((1003 : ℝ)/1000)/A := by gcongr
      _ = A^(-(1 : ℝ)/5+(1003 : ℝ)/1000)/A^(1 : ℝ) := by rw [← Real.rpow_add hA0,Real.rpow_one]
      _ = A^(-(1 : ℝ)/5+(1003 : ℝ)/1000-1) := (Real.rpow_sub hA0 _ _).symm
      _ = _ := by congr 1; norm_num
  have h2 : A^((1 : ℝ)/2)/B ≤ A^(-(1 : ℝ)/2) := by
    calc
      _ ≤ A^((1 : ℝ)/2)/A := by gcongr
      _ = A^((1 : ℝ)/2)/A^(1 : ℝ) := by rw [Real.rpow_one]
      _ = A^((1 : ℝ)/2-1) := (Real.rpow_sub hA0 _ _).symm
      _ = _ := by congr 1; norm_num
  have hsmall : A^(-(1 : ℝ)/2) ≤ A^(-(197 : ℝ)/1000) :=
    Real.rpow_le_rpow_of_exponent_le hA (by norm_num)
  have hsum : A^(-(1 : ℝ)/5)*κ/B+A^((1 : ℝ)/2)/B ≤ 2*A^(-(197 : ℝ)/1000) := by linarith only [h1,h2,hsmall]
  have hscale := mul_le_mul_of_nonneg_left hsum initialOldGateConstant_positive.le
  calc
    initialOldGate A κ B = initialOldGateConstant*(A^(-(1 : ℝ)/5)*κ/B+A^((1 : ℝ)/2)/B) := by
      unfold initialOldGate planarEpsilon
      ring
    _ ≤ initialOldGateConstant*(2*A^(-(197 : ℝ)/1000)) := hscale
    _ = (2*initialOldGateConstant)*A^(-(197 : ℝ)/1000) := by ring
    _ ≤ _ := hmargin

theorem eventually_initial_gate_covers_working : ∀ᶠ A : ℝ in atTop,
    ∀ K : ℝ, 0 < K → K ≤ A^((3 : ℝ)/1000) → workingGateFraction A ≤ initialGateConstant/K^2 := by
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    eventually_const_mul_power_le (by norm_num : -(16 : ℝ)/125 < 0) (1/initialGateConstant)]
    with A hA hmargin
  simp only [Real.rpow_zero] at hmargin
  intro K hK hKA
  have hsquare : K^2 ≤ A^((3 : ℝ)/500) := by
    have hh := (sq_le_sq₀ hK.le (Real.rpow_pos_of_pos hA ((3 : ℝ)/1000)).le).mpr hKA
    rw [← Real.rpow_mul_natCast hA.le] at hh
    norm_num at hh
    exact hh
  have hprod := mul_le_mul_of_nonneg_left hsquare (Real.rpow_pos_of_pos hA (-(67 : ℝ)/500)).le
  have he : A^(-(67 : ℝ)/500)*A^((3 : ℝ)/500) = A^(-(16 : ℝ)/125) := by
    rw [← Real.rpow_add hA]; congr 1; norm_num
  rw [he] at hprod
  have hc : A^(-(16 : ℝ)/125) ≤ initialGateConstant := by
    have hh : A^(-(16 : ℝ)/125)/initialGateConstant ≤ 1 := by
      calc
        _ = (1/initialGateConstant)*A^(-(16 : ℝ)/125) := by ring
        _ ≤ _ := hmargin
    have hh' := (div_le_iff₀ initialGateConstant_positive).mp hh
    simpa only [one_mul] using hh'
  exact (le_div_iff₀ (sq_pos_of_pos hK)).mpr (hprod.trans hc)

end
end StrongSilver
