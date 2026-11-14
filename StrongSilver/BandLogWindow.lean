-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.SqrtLinearMargins
import StrongSilver.BandPadBounds
import StrongSilver.CommonBandExponents
import StrongSilver.FinalAverageWindow

namespace StrongSilver
open Real Filter Set
noncomputable section
set_option maxHeartbeats 4000000

def outerBandLow (u : ℝ) : ℝ := u/bandRatio-3*Real.sqrt u
def outerBandHigh (u : ℝ) : ℝ := u+4*Real.sqrt u

/-- Uniform cutoff geometry for an enlarged paper band. The actual
cutoff is constructed by the inverse logarithmic transform. The pad,
source cutoff, branch, and power-gap requirements follow uniformly. -/
theorem eventually_outer_band_log_window : ∀ᶠ u : ℝ in atTop,
    ∀ B μ y : ℝ, 1 < B → u ≤ firstAverageLogScale B → 0 < μ → μ*B ≤ 1/2 →
    y ∈ Icc (outerBandLow u) (outerBandHigh u) →
    let P := Real.exp ((987:ℝ)/1000*u)
    let A := logarithmicCutoff μ P y
    P+Real.exp y ≤ B^(1-firstAverageEta) ∧ μ*(P+Real.exp y) ≤ 1/2 ∧ 0 < A ∧
      (999:ℝ)/1000*u ≤ Real.log A ∧ Real.log A ≤ (1001:ℝ)/1000*u ∧
      A^((49:ℝ)/50) ≤ P ∧ P ≤ A^((199:ℝ)/200) ∧ 2*P ≤ A ∧
      A ≤ B^(1-firstAverageEta) ∧ u/2 ≤ Real.log A ∧
      cappedStep μ B A = P+Real.exp y := by
  have hη := firstAverageEta_bounds.1
  have hηmax := firstAverageEta_bounds.2
  have hr := zero_lt_one.trans bandRatio_bounds.1
  have hrupper : bandRatio ≤ (10001:ℝ)/10000 := by
    unfold bandRatio
    linarith only [hηmax]
  filter_upwards [eventually_gt_atTop (0:ℝ),
    eventually_sqrt_affine_le_linear (by norm_num : (0:ℝ) < 1/1250) 3 (Real.log 2),
    eventually_sqrt_affine_le_linear (by norm_num : (0:ℝ) < 1/1000) 4 (Real.log 2),
    eventually_sqrt_affine_le_linear (by positivity : 0 < firstAverageEta/2) 4 (Real.log 2)]
    with u hu hlowMargin hhighMargin hglobalMargin
  intro B μ y hB hU hμ hμB hy
  let P := Real.exp ((987:ℝ)/1000*u)
  let A := logarithmicCutoff μ P y
  have hP : 0 < P := Real.exp_pos _
  have hlogB := Real.log_pos hB
  have hlog2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
  have hylo := hy.1
  have hyhi := hy.2
  have hratio : (9998:ℝ)/10000*u ≤ u/bandRatio := by
    apply (le_div_iff₀ hr).mpr
    have hc : (9998:ℝ)/10000*bandRatio ≤ 1 := by linarith only [hrupper]
    have hh := mul_le_mul_of_nonneg_right hc hu.le
    nlinarith only [hh]
  have hyLow : (999:ℝ)/1000*u ≤ y-Real.log 2 := by
    change u/bandRatio-3*Real.sqrt u ≤ y at hylo
    linarith only [hylo,hratio,hlowMargin]
  have hyHigh : y+Real.log 2 ≤ (1001:ℝ)/1000*u := by
    change y ≤ u+4*Real.sqrt u at hyhi
    linarith only [hyhi,hhighMargin]
  have hPy : P ≤ Real.exp y := by
    apply Real.exp_le_exp.mpr
    nlinarith only [hyLow,hlog2,hu]
  have hsum : P+Real.exp y ≤ 2*Real.exp y := by linarith only [hPy]
  have hsumExp : P+Real.exp y ≤ Real.exp (y+Real.log 2) := by
    rw [Real.exp_add,Real.exp_log (by norm_num : (0:ℝ) < 2)]
    nlinarith only [hsum]
  have hyGlobal : y+Real.log 2 ≤ (1-firstAverageEta)*Real.log B := by
    have h1 : y+Real.log 2 ≤ (1+firstAverageEta/2)*u := by
      change y ≤ u+4*Real.sqrt u at hyhi
      nlinarith only [hyhi,hglobalMargin]
    have h2 := mul_le_mul_of_nonneg_left hU (show 0 ≤ 1+firstAverageEta/2 by positivity)
    change (1+firstAverageEta/2)*u ≤ (1+firstAverageEta/2)*((1-2*firstAverageEta)*Real.log B) at h2
    have hcoef : (1+firstAverageEta/2)*(1-2*firstAverageEta) ≤ 1-firstAverageEta := by nlinarith only [hη]
    have h3 := mul_le_mul_of_nonneg_right hcoef hlogB.le
    nlinarith only [h1,h2,h3]
  have hglobal : P+Real.exp y ≤ B^(1-firstAverageEta) := by
    rw [Real.rpow_def_of_pos (zero_lt_one.trans hB)]
    exact hsumExp.trans (Real.exp_le_exp.mpr (by nlinarith only [hyGlobal]))
  have hpowerB : B^(1-firstAverageEta) ≤ B := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hB.le (show 1-firstAverageEta ≤ (1:ℝ) by linarith only [hη])
  have hsmall : μ*(P+Real.exp y) ≤ 1/2 :=
    (mul_le_mul_of_nonneg_left (hglobal.trans hpowerB) hμ.le).trans hμB
  have hA : 0 < A := logarithmicCutoff_positive hμ hP.le
  have hsize := logarithmicCutoff_size hμ hP.le hsmall
  have hAlower : Real.exp y/2 ≤ A := (div_le_div_of_nonneg_right (le_add_of_nonneg_left hP.le) (by norm_num : (0:ℝ) ≤ 2)).trans hsize.1
  have hAupper : A ≤ 2*Real.exp y := hsize.2.1.trans hsum
  have hlogLow := Real.log_le_log (div_pos (Real.exp_pos y) (by norm_num : (0:ℝ) < 2)) hAlower
  rw [Real.log_div (Real.exp_ne_zero _) (by norm_num : (2:ℝ) ≠ 0),Real.log_exp] at hlogLow
  have hlogHigh := Real.log_le_log hA hAupper
  rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (Real.exp_ne_zero _),Real.log_exp] at hlogHigh
  have hlo := hyLow.trans hlogLow
  have hhi : Real.log A ≤ (1001:ℝ)/1000*u := by linarith only [hlogHigh,hyHigh]
  have hlog2u : Real.log 2 ≤ u/1000 := by
    have hs := Real.sqrt_nonneg u
    linarith only [hhighMargin,hs]
  have hpad := band_pad_bounds hA hu.le hlo hhi hlog2u
  have hbranch : P+Real.exp y ≤ logarithmicStep μ B :=
    (hglobal.trans hpowerB).trans (logarithmicStep_ge hμ (by linarith only [hμB]))
  exact ⟨hglobal,hsmall,hA,hlo,hhi,hpad.1,hpad.2.1,hpad.2.2,hsize.2.1.trans hglobal,
    by nlinarith only [hlo,hu],cappedStep_cutoff hμ (by linarith only [hμB]) hbranch⟩

end
end StrongSilver
