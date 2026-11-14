-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PowerMargins
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Floor.Ring

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 3000000

/-- The logarithmic depth used in the two-gap improvement. -/
def fourPhaseDepth (u : ℝ) : ℕ := Nat.ceil (3*Real.log (Real.log u)/Real.log 2)

theorem fourPhaseDepth_bounds {u : ℝ} (hu : 1 ≤ Real.log u) :
    3*Real.log (Real.log u)/Real.log 2 ≤ (fourPhaseDepth u:ℝ) ∧
    (fourPhaseDepth u:ℝ) < 3*Real.log (Real.log u)/Real.log 2+1 := by
  have hlog : 0 ≤ Real.log (Real.log u) := Real.log_nonneg hu
  have hlog2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  exact ⟨Nat.le_ceil _,Nat.ceil_lt_add_one (div_nonneg (mul_nonneg (by norm_num) hlog) hlog2.le)⟩

/-- Exact quantitative comparison between the number of groups and the
cube of log u, including the natural-number rounding of the depth. -/
theorem fourPhaseDepth_group_count_bounds {u : ℝ} (hu : 1 ≤ Real.log u) :
    (Real.log u)^3 ≤ (2:ℝ)^fourPhaseDepth u ∧
      (2:ℝ)^fourPhaseDepth u ≤ 2*(Real.log u)^3 := by
  have hlog : 0 < Real.log u := zero_lt_one.trans_le hu
  have hx : (2:ℝ)^(3*Real.log (Real.log u)/Real.log 2) = (Real.log u)^3 := by
    have he : 3*Real.log (Real.log u)/Real.log 2 = Real.logb 2 ((Real.log u)^3) := by
      rw [Real.logb,Real.log_pow]
      norm_num
    rw [he]
    exact Real.rpow_logb (by norm_num) (by norm_num) (pow_pos hlog _)
  have hb := fourPhaseDepth_bounds hu
  have hlo := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hb.1
  have hhi := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hb.2.le
  rw [hx,Real.rpow_natCast] at hlo
  rw [Real.rpow_natCast,Real.rpow_add (by norm_num : (0:ℝ) < 2),hx,Real.rpow_one] at hhi
  exact ⟨hlo,by nlinarith only [hhi]⟩

/-- A common lower scale with denominator 4^(d+2) loses only the sixth
power of log u. This controls every negative-mass and height budget. -/
theorem fourPhaseDepth_scale_denominator {u : ℝ} (hu : 1 ≤ Real.log u) :
    (4:ℝ)^(fourPhaseDepth u+2) ≤ 64*(Real.log u)^6 := by
  have hb := (fourPhaseDepth_group_count_bounds hu).2
  have h0 : 0 ≤ (2:ℝ)^fourPhaseDepth u := pow_nonneg (by norm_num) _
  have hlog0 : 0 ≤ Real.log u := zero_le_one.trans hu
  have h1 : 0 ≤ 2*(Real.log u)^3 := by positivity
  have hsq : ((2:ℝ)^fourPhaseDepth u)^2 ≤ (2*(Real.log u)^3)^2 := (sq_le_sq₀ h0 h1).mpr hb
  have hpow : (4:ℝ)^fourPhaseDepth u = ((2:ℝ)^fourPhaseDepth u)^2 := by
    rw [show (4:ℝ) = 2*2 by norm_num,mul_pow,pow_two]
  rw [pow_add,hpow]
  norm_num
  nlinarith only [hsq]

theorem lower_scale_of_fourPhaseDepth {u M K : ℝ} (hu : 1 ≤ Real.log u) (hM : 0 ≤ M) (hK : 0 < K) :
    M/(64*K*(Real.log u)^6) ≤ M/(K*(4:ℝ)^(fourPhaseDepth u+2)) := by
  have hlog : 0 < Real.log u := zero_lt_one.trans_le hu
  apply div_le_div_of_nonneg_left hM (mul_pos hK (pow_pos (by norm_num) _))
  have hh := mul_le_mul_of_nonneg_left (fourPhaseDepth_scale_denominator hu) hK.le
  nlinarith only [hh]

end
end StrongSilver
