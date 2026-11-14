-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.OrdinaryPhaseParameters

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 2000000

/-- Ordinary phases with an explicit constant in the logarithmic loss (3.18).
The plane and scalar heights are constructed, rather than postulated. -/
theorem eventually_exists_ordinary_phase : ∀ᶠ A : ℝ in atTop,
    ∀ μ b T P : ℝ, ∀ h : List ℝ, OrdinaryPhaseParameters A μ b T P h →
      ∃ e : ℝ, 0 < e ∧ ∃ L : LocalPhaseCertificate A μ b T e h,
        e^2 = A^(-(3 : ℝ)/25)*T*(‖L.R‖+P) ∧
        L.terminalGate ≤ workingGateFraction A ∧
        workingGateFraction A*L.sourceSlopeCap ≤ ((1/T-μ)/32)*Real.exp (-2*negativeLogSum h T)*e^2 ∧
        ((b-P)/(transformedGapMaximum μ h+P))*Real.exp (-(1200/Real.log A+μ*transformedGapMaximum μ h)) ≤
          ‖L.path.x (Fin.last _)‖/‖L.path.x 0‖ := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),eventually_log_le_small_power,
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 499/500)).eventually (eventually_ge_atTop (8 : ℝ)),
    eventually_exists_local_phase,eventually_working_new_gate,eventually_working_old_gate,
    eventually_working_phase_norm] with A hA hlog hApow hex hnew hold hnorm
  intro μ b T P h W
  have hb8 : 8 ≤ b := hApow.trans W.pivot_lower
  have hb0 : 0 < b := by linarith
  have hT0 : 0 < T := hb0.trans W.b_lt_T
  have hAT0 := (div_le_iff₀ hT0).mp W.cap_ratio
  have hAT : A < T := by linarith
  have hμA1 : μ*A ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_left hAT0 W.mu_positive.le
    nlinarith only [hm,W.curvature]
  have hμT1 : μ*T < 1 := by linarith [W.curvature]
  obtain ⟨L0⟩ := hex μ b T 1 W.mu_positive hμA1 hb8 W.b_lt_T hAT zero_lt_one hμT1 h W.gap_cap
  have hA0 : 0 < A := zero_lt_one.trans hA
  have hP0 : 0 < P := (Real.rpow_pos_of_pos hA0 _).trans_le W.pad_lower
  obtain ⟨e,he0,he⟩ := L0.working_scalar_scale_exists hP0
  let L := L0.withScalarScale e he0
  have heL : e^2 = A^(-(3 : ℝ)/25)*T*(‖L.R‖+P) := he
  have hgateNew := hnew μ b T e h L P W.pad_lower W.cap_ratio W.curvature W.mass_time
    W.mass_pivot W.time_bound W.pivot_lower heL W.negative_charge
  have hgateOld := hold μ b T e h L hlog W.cap_ratio W.curvature W.mass_time W.mass_bound
    W.pivot_lower W.negative_charge
  have hN := hnorm μ b T e h L P W.pad_lower W.pivot_upper W.cap_ratio W.curvature W.mass_time
    W.mass_pivot W.time_bound heL
  have hpow : A^((199 : ℝ)/200) ≤ A^((499 : ℝ)/500) :=
    Real.rpow_le_rpow_of_exponent_le hA.le (by norm_num)
  have hPb : P ≤ b := W.pad_upper.trans (hpow.trans W.pivot_lower)
  have hP1 : 1 ≤ P := (Real.one_le_rpow hA.le (by norm_num : (0 : ℝ) ≤ 49/50)).trans W.pad_lower
  have hm := transformedGapMaximum_nonnegative L.mu_positive h L.small_steps
  have hM : 0 < transformedGapMaximum μ h+P := add_pos_of_nonneg_of_pos hm hP0
  have hX : L.path.x 0 ≠ 0 := L.path.source_ne_zero L.endpoint_ne_zero
  have hE : b-P ≤ ‖L.path.x (Fin.last _)‖ := by linarith [L.endpoint_norm_lower]
  exact ⟨e,he0,L,heL,hgateOld,hgateNew,
    ratio_lower_of_norm_upper (norm_pos_iff.mpr hX) hM (sub_nonneg.mpr hPb) hE hN⟩

end
end StrongSilver
