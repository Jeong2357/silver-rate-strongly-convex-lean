-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandProtectedWindowSums
import Mathlib.Algebra.Order.Floor.Ring

namespace StrongSilver
open Real Filter Set
noncomputable section
set_option maxHeartbeats 3400000

def bandBinWidth (u : ℝ) : ℝ := Real.log u/2

def bandBinCount (u : ℝ) : ℕ := Nat.ceil (2*u)+1

theorem eventually_band_bin_geometry : ∀ᶠ u : ℝ in atTop,
    1 ≤ outerBandLow u ∧ protectedBandHigh u ≤ 2*u ∧ 1 < bandBinWidth u ∧
    (bandBinCount u:ℝ) ≤ 3*u ∧
    ∀ height : ℝ, outerBandLow u+bandBinWidth u < height → height ≤ protectedBandHigh u →
      let j := Nat.floor height
      j < bandBinCount u ∧ (j:ℝ) ≤ height ∧ height < (j:ℝ)+1 ∧
        (j:ℝ)+1-bandBinWidth u ∈ Icc (outerBandLow u) (outerBandHigh u) := by
  filter_upwards [eventually_ge_atTop (4:ℝ),Real.tendsto_log_atTop.eventually_gt_atTop (2:ℝ),
    eventually_sqrt_affine_le_linear (by norm_num : (0:ℝ) < 1/4) 3 0,
    eventually_sqrt_affine_le_linear (by norm_num : (0:ℝ) < 1) 4 0] with u hu hlog hlo hhi
  have hu0 : 0 ≤ u := (by norm_num : (0:ℝ) ≤ 4).trans hu
  have hr := zero_lt_one.trans bandRatio_bounds.1
  have hdiv : u/2 ≤ u/bandRatio := by
    apply (le_div_iff₀ hr).mpr
    have hh := mul_le_mul_of_nonneg_right bandRatio_bounds.2.le hu0
    nlinarith only [hh]
  have ha : 1 ≤ outerBandLow u := by unfold outerBandLow; linarith only [hdiv,hlo,hu]
  have hb : protectedBandHigh u ≤ 2*u := by
    unfold protectedBandHigh outerBandHigh
    linarith only [hhi,visibilitySpacing_positive]
  have hw : 1 < bandBinWidth u := by unfold bandBinWidth; linarith only [hlog]
  have hc := Nat.ceil_lt_add_one (show (0:ℝ) ≤ 2*u by positivity)
  have hcount : (bandBinCount u:ℝ) ≤ 3*u := by
    dsimp only [bandBinCount]
    push_cast
    linarith only [hc,hu]
  refine ⟨ha,hb,hw,hcount,?_⟩
  intro height hlow hhigh
  dsimp only
  have hh0 : 0 ≤ height := by linarith only [ha,hw,hlow]
  have hjlo := Nat.floor_le hh0
  have hjhi := Nat.lt_floor_add_one height
  have hceil : (Nat.floor height:ℝ) ≤ (Nat.ceil (2*u):ℝ) :=
    hjlo.trans ((hhigh.trans hb).trans (Nat.le_ceil (2*u)))
  have hNat : Nat.floor height ≤ Nat.ceil (2*u) := by exact_mod_cast hceil
  refine ⟨by unfold bandBinCount; omega,hjlo,hjhi,?_,?_⟩
  · linarith only [hjhi,hlow]
  · have hp : protectedBandHigh u ≤ outerBandHigh u := by unfold protectedBandHigh; linarith only [visibilitySpacing_positive]
    linarith only [hjlo,hw,hhigh,hp]

end
end StrongSilver
