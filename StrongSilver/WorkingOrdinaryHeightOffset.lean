-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.WorkingOrdinarySourceCap
import StrongSilver.OrdinaryPhaseParameters
import StrongSilver.ScalarPaddingPower
import StrongSilver.QuadraticPaddingPower

namespace StrongSilver.LocalPhaseCertificate
open Real
noncomputable section
set_option maxHeartbeats 2400000

/-- A decaying bound for the ordinary attachment height offset. The
relative bound suffices for the two-gap construction without requiring
the sharp exponent of the paper's intermediate estimate. -/
theorem working_source_height_offset_bound {A μ b T e P : ℝ} {h : List ℝ}
    (L : LocalPhaseCertificate A μ b T e h) (hA : 1 ≤ A)
    (W : OrdinaryPhaseParameters A μ b T P h)
    (he : e^2 = A^(-(3 : ℝ)/25)*T*(‖L.R‖+P)) :
    L.sourceHeightOffset ≤ 3*workingAnalyticConstant^2*A^(-(37 : ℝ)/500)*(‖L.R‖+P)^2 := by
  let K := workingAnalyticConstant
  let Q := ‖L.R‖+P
  let C := scalarRampGrowth T A b h
  have hA0 := zero_lt_one.trans_le hA
  have hK : 1 ≤ K := workingAnalyticConstant_ge_one
  have hP : 0 ≤ P := (Real.rpow_pos_of_pos hA0 _).le.trans W.pad_lower
  have hQ : A^((49 : ℝ)/50) ≤ Q := W.pad_lower.trans (le_add_of_nonneg_left (norm_nonneg L.R))
  have hJ := L.working_terminalInner_bound hA W.cap_ratio W.curvature W.mass_time
  have hq := L.working_q_bound W.cap_ratio W.curvature W.mass_time
  have hC := L.working_growth_bound_constant hA W.cap_ratio W.mass_time W.mass_pivot
  have hD := quadratic_padding_power_bound hA hK (by linarith [L.b_large]) (norm_nonneg L.R)
    (le_add_of_nonneg_right hP) L.terminalInner_nonnegative W.pivot_upper hQ hJ hq L.pad
  have hCe : 0 ≤ C*e := mul_nonneg L.growth_positive.le L.e_positive.le
  have hscalar := scalar_padding_power_bound hA0 (zero_le_one.trans hK) L.growth_positive.le L.e_positive.le
    hCe (le_refl (C*e)) hC W.time_bound hQ he
  have hstart : L.scalar.x ≤ C*e := by
    simpa only [List.take_zero,iterate_nil] using (L.scalar.estimates 0 (by omega)).2.1
  have hax := mul_le_mul_of_nonneg_right hstart hCe
  have hExp : Real.exp (negativeLogSum h T) ≤ A^((1 : ℝ)/250) := by
    rw [Real.rpow_def_of_pos hA0]
    exact Real.exp_le_exp.mpr (by nlinarith only [W.negative_charge])
  have hDprod := mul_le_mul hExp hD (sq_nonneg L.D) (Real.rpow_pos_of_pos hA0 ((1 : ℝ)/250)).le
  have hpow : A^((1 : ℝ)/250)*A^(-(7 : ℝ)/40) = A^(-(171 : ℝ)/1000) := by
    rw [← Real.rpow_add hA0]; congr 1; norm_num
  have hdecay : A^(-(171 : ℝ)/1000) ≤ A^(-(37 : ℝ)/500) := Real.rpow_le_rpow_of_exponent_le hA (by norm_num)
  have hdecayQ := mul_le_mul_of_nonneg_right hdecay (sq_nonneg Q)
  have hdecayK := mul_le_mul_of_nonneg_left hdecayQ (show 0 ≤ 2*K^2 by positivity)
  have heq : A^((1 : ℝ)/250)*(2*K^2*A^(-(7 : ℝ)/40)*Q^2) = 2*K^2*A^(-(171 : ℝ)/1000)*Q^2 := by
    rw [← hpow]; ring
  change Real.exp (negativeLogSum h T)*L.D^2 ≤ A^((1 : ℝ)/250)*(2*K^2*A^(-(7 : ℝ)/40)*Q^2) at hDprod
  rw [heq] at hDprod
  change Real.exp (negativeLogSum h T)*L.D^2+L.scalar.x*(C*e) ≤ _
  change (C*e)^2 ≤ K^2*A^(-(37 : ℝ)/500)*Q^2 at hscalar
  change _ ≤ 3*K^2*A^(-(37 : ℝ)/500)*Q^2
  nlinarith only [hDprod,hdecayK,hscalar,hax]

end
end StrongSilver.LocalPhaseCertificate
