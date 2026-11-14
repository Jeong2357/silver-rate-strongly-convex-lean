-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandLogWindow
import StrongSilver.BandEligibleSteps

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 3000000

/-- The pad is exponentially smaller than every actual selected factor
in the outer height window. This statement is pure band geometry. -/
theorem eventually_band_pad_ratio : ∀ᶠ u : ℝ in atTop, 1 ≤ bandPad u ∧
    ∀ y : ℝ, outerBandLow u ≤ y → bandPad u/Real.exp y ≤ Real.exp (-u/100) := by
  have hr := zero_lt_one.trans bandRatio_bounds.1
  have hrupper : bandRatio ≤ (10001:ℝ)/10000 := by
    unfold bandRatio
    linarith only [firstAverageEta_bounds.2]
  filter_upwards [eventually_ge_atTop (0:ℝ),
    eventually_sqrt_affine_le_linear (by norm_num : (0:ℝ) < 1/1000) 3 0] with u hu hsmall
  have hl : (9998:ℝ)/10000*u ≤ u/bandRatio := by
    apply (le_div_iff₀ hr).mpr
    have hc : (9998:ℝ)/10000*bandRatio ≤ 1 := by linarith only [hrupper]
    have hh := mul_le_mul_of_nonneg_right hc hu
    nlinarith only [hh]
  refine ⟨Real.one_le_exp_iff.mpr (by positivity),?_⟩
  intro y hy
  change u/bandRatio-3*Real.sqrt u ≤ y at hy
  have hy0 : (998:ℝ)/1000*u ≤ y := by linarith only [hy,hl,hsmall,hu]
  unfold bandPad
  rw [← Real.exp_sub]
  apply Real.exp_le_exp.mpr
  linarith only [hy0,hu]

/-- Exponential decay absorbs the outer-band O(W u) total weight. -/
theorem eventually_exp_negative_linear_le_inverse {c : ℝ} (hc : 0 < c) :
    ∀ᶠ u : ℝ in atTop, Real.exp (-c*u) ≤ 1/u := by
  have hh := Real.tendsto_exp_atTop.eventually (eventually_const_mul_negative_power_le_inverse_log (neg_neg_of_pos hc) (1:ℝ))
  filter_upwards [hh] with u hu
  rw [one_mul,Real.rpow_def_of_pos (Real.exp_pos u),Real.log_exp] at hu
  simpa only [mul_comm u (-c)] using hu

/-- In particular the canonical offset-change input is valid uniformly
on all nodes of the outer band. -/
theorem eventually_band_pad_small : ∀ᶠ u : ℝ in atTop,
    1 ≤ bandPad u ∧ ∀ y : ℝ, outerBandLow u ≤ y →
      bandPad u ≤ Real.exp y/4 ∧ bandPad u/Real.exp y ≤ 1/u := by
  filter_upwards [eventually_band_pad_ratio,
    eventually_exp_negative_linear_le_inverse (by norm_num : (0:ℝ) < 1/100),eventually_ge_atTop (4:ℝ)]
    with u hgeom hinv hu
  have hu0 : 0 < u := lt_of_lt_of_le (by norm_num) hu
  refine ⟨hgeom.1,?_⟩
  intro y hy
  have hr := hgeom.2 y hy
  rw [show -u/100 = -((1:ℝ)/100)*u by ring] at hr
  have hri := hr.trans hinv
  have hquarter : (1:ℝ)/u ≤ 1/4 := by
    apply (div_le_iff₀ hu0).mpr
    linarith only [hu]
  have hp := (div_le_iff₀ (Real.exp_pos y)).mp (hri.trans hquarter)
  exact ⟨by linear_combination hp,hri⟩

end
end StrongSilver
