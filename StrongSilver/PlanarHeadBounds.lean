-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PlanarAsymptotics
import StrongSilver.ArcBodyBounds

namespace StrongSilver
open Real Set Filter
noncomputable section

theorem planar_head_radius_upper {ε k₀ : ℝ} (hε : 0 < ε) (hk : 0 < k₀)
    (hεk : ε ≤ k₀) (hk1 : k₀ ≤ 1/16) :
    explicitArcRadius (Real.arctan ε⁻¹) (Real.sqrt (1+ε^2)) k₀ 0 ≤ 1+6*k₀ := by
  let Θ := Real.arctan ε⁻¹
  have hΘ0 : 0 ≤ Θ := (Real.arctan_pos.mpr (inv_pos.mpr hε)).le
  have hΘ2 : Θ ≤ 2 := by
    have hh := Real.arctan_lt_pi_div_two ε⁻¹
    dsimp [Θ]
    linarith [Real.pi_lt_four]
  have hε1 : ε ≤ 1 := hεk.trans (by linarith)
  have hεsq : ε^2 ≤ k₀ := by
    have hh := mul_le_mul_of_nonneg_left hε1 hε.le
    nlinarith only [hh,hεk]
  have hR : Real.sqrt (1+ε^2) ≤ 1+k₀ := by
    have hs := Real.sq_sqrt (show 0 ≤ 1+ε^2 by positivity)
    have hn := Real.sqrt_nonneg (1+ε^2)
    nlinarith only [hs,hn,hεsq,hk,sq_nonneg k₀]
  have hx0 : 0 ≤ k₀*Θ := mul_nonneg hk.le hΘ0
  have hx1 : k₀*Θ ≤ 1 := by
    have hh := mul_le_mul hk1 hΘ2 hΘ0 (by norm_num : (0 : ℝ) ≤ 1/16)
    norm_num at hh
    linarith
  have hexp := Real.abs_exp_sub_one_le (show |k₀*Θ| ≤ 1 by rwa [abs_of_nonneg hx0])
  rw [abs_of_nonneg hx0] at hexp
  have hexpu : Real.exp (k₀*Θ) ≤ 1+4*k₀ := by
    have hh := (le_abs_self (Real.exp (k₀*Θ)-1)).trans hexp
    nlinarith only [hh,mul_le_mul_of_nonneg_left hΘ2 hk.le]
  have hradius := explicitArcRadius_uniform_upper (R := Real.sqrt (1+ε^2)) hk (by linarith : k₀ ≤ 1/2)
    (Real.arctan_lt_pi_div_two ε⁻¹) (Real.sqrt_nonneg (1+ε^2)) ⟨le_rfl,hΘ0⟩
  have hprod := mul_le_mul hR hexpu (Real.exp_pos (k₀*Θ)).le (by linarith : 0 ≤ 1+k₀)
  have hsmall := mul_nonneg hk.le (show 0 ≤ 1-4*k₀ by linarith)
  nlinarith only [hradius,hprod,hsmall]

theorem eventually_planar_head_radius : ∀ᶠ A : ℝ in atTop,
    explicitArcRadius (planarTerminalAngle A) (planarTerminalRadius A) (planarSlopeScale A) 0 ≤
      1+600/Real.log A := by
  filter_upwards [planar_parameters_eventually] with A hparams
  obtain ⟨hA,hlog,hεk,hsmall⟩ := hparams
  have hAl := Real.log_pos hA
  have hε : 0 < planarEpsilon A := Real.rpow_pos_of_pos (zero_lt_one.trans hA) _
  have hk : 0 < planarSlopeScale A := div_pos (by norm_num) hAl
  have hk1 : planarSlopeScale A ≤ 1/16 := (div_le_iff₀ hAl).mpr (by linarith)
  have hh := planar_head_radius_upper hε hk hεk hk1
  change explicitArcRadius (Real.arctan (planarEpsilon A)⁻¹) (Real.sqrt (1+(planarEpsilon A)^2)) (planarSlopeScale A) 0 ≤ _
  convert hh using 1 <;> unfold planarSlopeScale <;> ring

end
end StrongSilver
