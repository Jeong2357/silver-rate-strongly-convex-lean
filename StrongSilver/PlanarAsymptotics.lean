-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PlanarParameterBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace StrongSilver
open Real Set Filter
open scoped Topology
noncomputable section

theorem planarEpsilon_division_powers {A : ℝ} (hA : 0 < A) :
    (1/A)/planarEpsilon A = A^(-(4 : ℝ)/5) ∧
    ((1/A)*A^((9 : ℝ)/20))/(planarEpsilon A)^2 = A^(-(3 : ℝ)/20) := by
  have hone : 1/A = A^(-1 : ℝ) := by rw [Real.rpow_neg_one,one_div]
  have heps : (planarEpsilon A)^2 = A^(-(2 : ℝ)/5) := by
    unfold planarEpsilon
    rw [← Real.rpow_mul_natCast hA.le]
    congr 1
    norm_num
  constructor
  · rw [hone,planarEpsilon,← Real.rpow_sub hA]
    congr 1
    norm_num
  · rw [hone,heps,← Real.rpow_add hA,← Real.rpow_sub hA]
    congr 1
    norm_num

theorem planarPerturbationSize_power_bound {A μ : ℝ} (hA : 1 < A) (hlog : 1600 ≤ Real.log A)
    (hμ : 0 ≤ μ) (hμA : μ*A ≤ 1) :
    planarPerturbationSize μ (planarEpsilon A) (planarTerminalAngle A) (planarTerminalRadius A) (planarSlopeScale A) ≤
      6*A^(-(4 : ℝ)/5)+576*A^(-(3 : ℝ)/20) := by
  have hApos : 0 < A := zero_lt_one.trans hA
  have hlogpos := Real.log_pos hA
  have hμbound : μ ≤ 1/A := (le_div_iff₀ hApos).mpr hμA
  have hε : 0 < planarEpsilon A := Real.rpow_pos_of_pos hApos _
  have hk : 0 < planarSlopeScale A := div_pos (by norm_num) hlogpos
  have hk1 : planarSlopeScale A ≤ 1/16 := (div_le_iff₀ hlogpos).mpr (by linarith)
  have hcoef : 1+(planarSlopeScale A)^2 ≤ 2 := by nlinarith [sq_nonneg (planarSlopeScale A)]
  have hM := planarComparisonBound_power_bound hA hlog
  have hΘ0 : 0 ≤ planarTerminalAngle A := (Real.arctan_pos.mpr (inv_pos.mpr hε)).le
  have hM0 : 0 ≤ planarComparisonBound (planarTerminalAngle A) (planarTerminalRadius A) (planarSlopeScale A) := by
    dsimp [planarComparisonBound,planarTerminalRadius]
    positivity
  obtain ⟨hpow1,hpow2⟩ := planarEpsilon_division_powers hApos
  unfold planarPerturbationSize
  calc
    _ ≤ 3*(1/A)*2/planarEpsilon A+
        18*(1/A)*2*(16*A^((9 : ℝ)/20))/(planarEpsilon A)^2 := by
      gcongr
    _ = 6*A^(-(4 : ℝ)/5)+576*A^(-(3 : ℝ)/20) := by
      rw [← hpow1,← hpow2]
      ring

theorem planarPerturbationScale_power_bound {A μ : ℝ} (hA : 1 < A) (hlog : 1600 ≤ Real.log A)
    (hμ : 0 ≤ μ) (hμA : μ*A ≤ 1) :
    planarPerturbationSize μ (planarEpsilon A) (planarTerminalAngle A) (planarTerminalRadius A) (planarSlopeScale A)*planarTerminalAngle A ≤
      12*A^(-(4 : ℝ)/5)+1152*A^(-(3 : ℝ)/20) := by
  have hδ := planarPerturbationSize_power_bound hA hlog hμ hμA
  have hΘ0 : 0 ≤ planarTerminalAngle A :=
    (Real.arctan_pos.mpr (inv_pos.mpr (Real.rpow_pos_of_pos (zero_lt_one.trans hA) _))).le
  have hΘ2 : planarTerminalAngle A ≤ 2 := by
    have hh := Real.arctan_lt_pi_div_two (planarEpsilon A)⁻¹
    unfold planarTerminalAngle
    linarith [Real.pi_lt_four]
  have hb : 0 ≤ 6*A^(-(4 : ℝ)/5)+576*A^(-(3 : ℝ)/20) := by positivity
  have hh := mul_le_mul hδ hΘ2 hΘ0 hb
  nlinarith only [hh]

theorem planar_parameters_eventually : ∀ᶠ A : ℝ in atTop,
    1 < A ∧ 1600 ≤ Real.log A ∧ planarEpsilon A ≤ planarSlopeScale A ∧
      ∀ μ : ℝ, 0 ≤ μ → μ*A ≤ 1 →
        (5 : ℝ)/4*Real.exp
          (planarPerturbationSize μ (planarEpsilon A) (planarTerminalAngle A) (planarTerminalRadius A) (planarSlopeScale A)*planarTerminalAngle A) ≤ 2 := by
  have hratio : Tendsto (fun A : ℝ => Real.log A/A^((1 : ℝ)/5)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1/5)).tendsto_div_nhds_zero
  have hdecay : Tendsto (fun A : ℝ => 12*A^(-(4 : ℝ)/5)+1152*A^(-(3 : ℝ)/20)) atTop (𝓝 0) := by
    convert! ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 4/5)).const_mul 12).add
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3/20)).const_mul 1152) using 1 <;> norm_num
  have hlogpos : 0 < Real.log ((8 : ℝ)/5) := Real.log_pos (by norm_num)
  filter_upwards [eventually_gt_atTop (1 : ℝ),Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1600 : ℝ)),
    (tendsto_order.1 hratio).2 100 (by norm_num),
    (tendsto_order.1 hdecay).2 (Real.log ((8 : ℝ)/5)) hlogpos] with A hA hlog hrat hdec
  have hApos : 0 < A := zero_lt_one.trans hA
  have hAl : 0 < Real.log A := Real.log_pos hA
  have hε : 0 < planarEpsilon A := Real.rpow_pos_of_pos hApos _
  have heps : planarEpsilon A ≤ planarSlopeScale A := by
    apply (le_div_iff₀ hAl).mpr
    have he : planarEpsilon A*Real.log A = Real.log A/A^((1 : ℝ)/5) := by
      unfold planarEpsilon
      rw [show -(1 : ℝ)/5 = -((1 : ℝ)/5) by ring,Real.rpow_neg hApos.le]
      ring
    rw [he]
    exact hrat.le
  refine ⟨hA,hlog,heps,fun μ hμ hμA => ?_⟩
  have hδ := planarPerturbationScale_power_bound hA hlog hμ hμA
  have hh := Real.exp_le_exp.mpr (hδ.trans hdec.le)
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 8/5)] at hh
  nlinarith only [hh]

end
end StrongSilver
