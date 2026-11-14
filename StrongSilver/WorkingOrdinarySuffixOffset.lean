-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.WorkingOrdinaryHeightOffset

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 2400000

/-- A weaker negative power than the paper's intermediate A^(-.10)
is sufficient for the later polylogarithmic group estimates. -/
theorem eventually_working_suffix_offset_decay : ∀ᶠ A : ℝ in atTop,
    ∀ μ b T e P : ℝ, ∀ h : List ℝ, ∀ L : LocalPhaseCertificate A μ b T e h,
    OrdinaryPhaseParameters A μ b T P h →
    e^2 = A^(-(3 : ℝ)/25)*T*(‖L.R‖+P) → P ≤ ‖L.R‖ →
    L.sourceSlopeCap ≤ 8*‖L.R‖ ∧
    (L.sourceHeightOffset+‖L.R‖*(workingGateFraction A*L.sourceSlopeCap))/‖L.path.x 0‖^2 ≤ A^(-(1 : ℝ)/20) := by
  let K := workingAnalyticConstant
  filter_upwards [eventually_ge_atTop (1:ℝ),eventually_working_source_slope_cap,
    eventually_const_mul_power_le (by norm_num : -(37:ℝ)/500 < -(1:ℝ)/20) (12*K^2+6)]
    with A hA hcap hdecay
  intro μ b T e P h L W he hPM
  have hs := hcap μ b T e h L P W.pad_lower W.cap_ratio W.mass_time W.mass_pivot W.time_bound W.pivot_lower he
  have hH := L.working_source_height_offset_bound hA W he
  have hP : 0 ≤ P := (Real.rpow_pos_of_pos (zero_lt_one.trans_le hA) _).le.trans W.pad_lower
  have hR : 0 ≤ ‖L.R‖ := norm_nonneg _
  have hnorm : ‖L.R‖^2 ≤ ‖L.path.x 0‖^2 := by
    rw [L.start,phase_norm_sq]; nlinarith only [sq_nonneg L.D,sq_nonneg L.scalar.x]
  have hX : 0 < ‖L.path.x 0‖^2 := sq_pos_of_pos
    (norm_pos_iff.mpr (L.path.source_ne_zero L.endpoint_ne_zero))
  have hQ : (‖L.R‖+P)^2 ≤ 4*‖L.path.x 0‖^2 := by
    have hmul := mul_le_mul_of_nonneg_right hPM (show 0 ≤ ‖L.R‖+P by linarith only [hR,hP])
    have hPR := mul_le_mul_of_nonneg_left hPM hR
    nlinarith only [hmul,hPR,hnorm]
  have hMQ : ‖L.R‖*(‖L.R‖+P) ≤ 2*‖L.path.x 0‖^2 := by
    have hh := mul_le_mul_of_nonneg_left hPM hR
    nlinarith only [hh,hnorm]
  have hpow : 0 ≤ A^(-(37:ℝ)/500) := (Real.rpow_pos_of_pos (zero_lt_one.trans_le hA) _).le
  have hη : 0 ≤ workingGateFraction A := (Real.rpow_pos_of_pos (zero_lt_one.trans_le hA) _).le
  have hηpow : workingGateFraction A ≤ A^(-(37:ℝ)/500) := by
    unfold workingGateFraction
    exact Real.rpow_le_rpow_of_exponent_le hA (by norm_num)
  have hHbound := mul_le_mul_of_nonneg_left hQ (show 0 ≤ 3*K^2*A^(-(37:ℝ)/500) by positivity)
  have hd1 := mul_le_mul_of_nonneg_left hs (mul_nonneg hR hη)
  have hd2 := mul_le_mul_of_nonneg_left hMQ hη
  have hd3 := mul_le_mul_of_nonneg_right hηpow (sq_nonneg ‖L.path.x 0‖)
  have hdecayX := mul_le_mul_of_nonneg_right hdecay (sq_nonneg ‖L.path.x 0‖)
  refine ⟨by nlinarith only [hs,hPM,hR],?_⟩
  apply (div_le_iff₀ hX).mpr
  change L.sourceHeightOffset ≤ 3*K^2*A^(-(37:ℝ)/500)*(‖L.R‖+P)^2 at hH
  nlinarith only [hH,hHbound,hd1,hd2,hd3,hdecayX]

end
end StrongSilver
