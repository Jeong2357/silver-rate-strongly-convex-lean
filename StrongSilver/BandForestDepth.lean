-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandBadWeightRate
import StrongSilver.FourPhaseDepthAsymptotics

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 3200000

/-- The rounded logarithmic depth times the actual band tolerance tends
to zero, with any prescribed absolute margin. -/
theorem eventually_band_depth_tolerance {ε : ℝ} (hε : 0 < ε) : ∀ᶠ u : ℝ in atTop,
    ((fourPhaseDepth u:ℝ)+4)*bandTolerance u ≤ ε := by
  have h1 := eventually_const_mul_log_pow_mul_power_le 0 (1:ℝ) (by norm_num : -(1:ℝ)/20 < 0)
    (show 0 < ε/2 by positivity)
  have h2 := eventually_const_mul_log_pow_mul_power_le 0 (4:ℝ) (by norm_num : -(1:ℝ)/10 < 0)
    (show 0 < ε/2 by positivity)
  filter_upwards [eventually_fourPhaseDepth_le_power (by norm_num : (0:ℝ) < 1/20),
    h1,h2,eventually_gt_atTop (0:ℝ)] with u hd hu1 hu2 hu
  have hδ : 0 ≤ bandTolerance u := (Real.rpow_pos_of_pos hu _).le
  have hh := mul_le_mul_of_nonneg_right hd hδ
  have he : u^((1:ℝ)/20)*bandTolerance u = u^(-(1:ℝ)/20) := by
    unfold bandTolerance
    rw [← Real.rpow_add hu]
    norm_num
  rw [he] at hh
  simp only [pow_zero,mul_one,one_mul] at hu1 hu2
  change 4*bandTolerance u ≤ ε/2 at hu2
  nlinarith only [hh,hu1,hu2]

/-- Good components in any of the depth windows have at most k+2
levels. The rounding margin is uniform for all k≤d+2. -/
theorem eventually_band_forest_spacing : ∀ᶠ u : ℝ in atTop,
    0 ≤ bandTolerance u ∧ bandTolerance u ≤ 1/100 ∧ 0 < Real.log rho-11*bandTolerance u ∧
    ∀ k : ℕ, k ≤ fourPhaseDepth u+2 →
      (k:ℝ)*Real.log rho < ((k+2:ℕ):ℝ)*(Real.log rho-11*bandTolerance u) := by
  have hω := log_rho_positive
  filter_upwards [eventually_band_depth_tolerance (show 0 < Real.log rho/100 by positivity),
    eventually_gt_atTop (0:ℝ)] with u hdepth hu
  have hδ : 0 ≤ bandTolerance u := (Real.rpow_pos_of_pos hu _).le
  have hd : (0:ℝ) ≤ fourPhaseDepth u := Nat.cast_nonneg _
  have hprod := mul_nonneg hd hδ
  have hδω : 11*bandTolerance u ≤ Real.log rho/8 := by nlinarith only [hdepth,hprod,hω]
  have hδ100 : bandTolerance u ≤ 1/100 := by
    have hlogrho : Real.log rho ≤ 2 := (Real.log_le_sub_one_of_pos rho_positive).trans (by linarith only [rho_bounds.2])
    nlinarith only [hdepth,hprod,hlogrho]
  refine ⟨hδ,hδ100,by linarith only [hδω,hω],?_⟩
  intro k hk
  have hkr : (k:ℝ) ≤ (fourPhaseDepth u:ℝ)+2 := by exact_mod_cast hk
  have hh := mul_le_mul_of_nonneg_right (show (k:ℝ)+2 ≤ (fourPhaseDepth u:ℝ)+4 by linarith only [hkr]) hδ
  have hlast : ((k:ℝ)+2)*bandTolerance u ≤ Real.log rho/22 := by nlinarith only [hh,hdepth,hω]
  push_cast
  nlinarith only [hlast,hω]

end
end StrongSilver
