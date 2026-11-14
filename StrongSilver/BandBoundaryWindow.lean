-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ExponentialWindowUpper
import StrongSilver.SilverKernelIntegral
import StrongSilver.BandForestDepth
import StrongSilver.WindowNormalizedPower

namespace StrongSilver
open ScheduleTree BinaryForest Real Filter Set MeasureTheory
noncomputable section
set_option maxHeartbeats 6200000

/-- A slightly enlarged half-open boundary strip, used to dominate
closed disagreement strips without imposing endpoint exceptions. -/
def bandBoundaryWindow (u z : ℝ) (k : ℕ) (y : ℝ) : ℝ :=
  exponentialWindow nu (z+(k:ℝ)*Real.log rho-22*(k:ℝ)*bandTolerance u)
    (z+(k:ℝ)*Real.log rho+22*(k:ℝ)*bandTolerance u) y

theorem bandBoundaryWindow_integrable (u z a b : ℝ) (k : ℕ) :
    IntervalIntegrable (bandBoundaryWindow u z k) volume a b := exponentialWindow_integrable _ _ _ _ _

/-- The exponential weight of a depth-k disagreement strip is
O(2^k * k*delta) times the original vertex weight, uniformly in k. -/
theorem eventually_band_boundary_window_integral : ∃ C > 0, ∀ᶠ u : ℝ in atTop,
    ∀ z a b : ℝ, ∀ k : ℕ, a ≤ b → k ≤ fourPhaseDepth u+2 →
    (∫ y in a..b, bandBoundaryWindow u z k y) ≤
      C*(2:ℝ)^k*(k:ℝ)*bandTolerance u*Real.exp (nu*z) := by
  refine ⟨44*Real.exp 22,by positivity,?_⟩
  filter_upwards [eventually_band_depth_tolerance (by norm_num : (0:ℝ) < 1),eventually_gt_atTop (0:ℝ)] with u hDepth hu
  intro z a b k hab hk
  have hδ : 0 ≤ bandTolerance u := (Real.rpow_pos_of_pos hu _).le
  have hkr : (k:ℝ) ≤ (fourPhaseDepth u:ℝ)+4 := by exact_mod_cast (show k ≤ fourPhaseDepth u+4 by omega)
  have hSmall := (mul_le_mul_of_nonneg_right hkr hδ).trans hDepth
  have hRad : 0 ≤ 22*(k:ℝ)*bandTolerance u := by positivity
  have hL : z+(k:ℝ)*Real.log rho-22*(k:ℝ)*bandTolerance u ≤
      z+(k:ℝ)*Real.log rho+22*(k:ℝ)*bandTolerance u := by linarith only [hRad]
  have hIntegral := exponentialWindow_integral_upper nu _ _ a b nu_positive hL hab
  have hνr : nu*(22*(k:ℝ)*bandTolerance u) ≤ 22 := by
    have hh := mul_le_mul_of_nonneg_left hSmall (show 0 ≤ 22*nu by have hn := nu_positive; positivity)
    have hν := nu_lt_one
    nlinarith only [hh,hν]
  have hExp : Real.exp (nu*(z+(k:ℝ)*Real.log rho+22*(k:ℝ)*bandTolerance u)) ≤
      Real.exp (nu*z)*(2:ℝ)^k*Real.exp 22 := by
    rw [mul_add,mul_add,Real.exp_add,Real.exp_add,silver_exp_nat_spacing]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hνr)
      (mul_nonneg (Real.exp_pos _).le (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) k))
  have hScale := mul_le_mul_of_nonneg_left hExp (show 0 ≤ 44*(k:ℝ)*bandTolerance u by positivity)
  change (∫ y in a..b, exponentialWindow nu _ _ y) ≤ _
  linear_combination hIntegral+hScale

/-- Closed error strips from the depth comparison fit strictly inside
the enlarged half-open window whenever k and the tolerance are positive. -/
theorem bandBoundaryWindow_dominates {u z y : ℝ} {k : ℕ} (hu : 0 < u) (hk : 1 ≤ k)
    (hStrip : |y-z-(k:ℝ)*Real.log rho| ≤ (k:ℝ)*(11*bandTolerance u)) :
    Real.exp (nu*y) ≤ bandBoundaryWindow u z k y := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast (Nat.zero_lt_of_lt hk)
  have hδ : 0 < bandTolerance u := Real.rpow_pos_of_pos hu _
  have hRad : 0 < (k:ℝ)*bandTolerance u := mul_pos hk0 hδ
  have hLo := (abs_le.mp hStrip).1
  have hHi := (abs_le.mp hStrip).2
  unfold bandBoundaryWindow
  rw [exponentialWindow_eq _ _ _ _ (by linarith only [hRad])]
  rw [if_pos (show z+(k:ℝ)*Real.log rho-22*(k:ℝ)*bandTolerance u ≤ y ∧
    y < z+(k:ℝ)*Real.log rho+22*(k:ℝ)*bandTolerance u from ⟨by nlinarith only [hLo,hRad],by nlinarith only [hHi,hRad]⟩)]

end
end StrongSilver
