-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ScalarPaddingLinear
import StrongSilver.WorkingEndpointCap
import StrongSilver.OrdinaryPhaseParameters

namespace StrongSilver
open Real Filter Complex
noncomputable section
set_option maxHeartbeats 2000000

theorem eventually_working_padding_linear : ∀ᶠ A : ℝ in atTop,
    ∀ μ b T e P₀ : ℝ, ∀ h : List ℝ, OrdinaryPhaseParameters A μ b T P₀ h →
      ∀ L : LocalPhaseCertificate A μ b T e h, ∀ P : ℝ, 0 ≤ P →
      e^2 = A^(-(3 : ℝ)/25)*T*(‖L.R‖+P) →
      ‖L.R‖ ≤ A^(3 : ℝ) ∧ L.D^2 ≤ A^(6 : ℝ) ∧
      L.scalar.x^2 ≤ A*(‖L.R‖+P) ∧ ‖L.path.x 0‖^2 ≤ A^(8 : ℝ)*(1+P) := by
  let K := workingAnalyticConstant
  have hK : 1 ≤ K := workingAnalyticConstant_ge_one
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  filter_upwards [eventually_ge_atTop (1 : ℝ),eventually_working_planar_all_power,
    eventually_const_mul_power_le (by norm_num : (453 : ℝ)/500 < 1) (K^2),
    eventually_const_mul_power_le (by norm_num : (5 : ℝ) < 6) (2*K),
    eventually_const_mul_power_le (by norm_num : (7 : ℝ) < 8) 4]
    with A hA hplanar hscalar hpad hsum
  intro μ b T e P₀ h W L P hP he
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  have hR : ‖L.R‖ ≤ A^(3 : ℝ) := by
    simpa only [List.take_zero,iterate_nil] using hplanar μ b T e h L W.cap_ratio W.curvature W.mass_time W.mass_bound 0
  have hJ : L.terminalInner ≤ 2*A^(3 : ℝ) := by
    have hh := (real_inner_le_norm L.R (⟨planarEpsilon A,1⟩ : ℂ)).trans
      (mul_le_mul hR L.terminal_planar_norm_le_two (norm_nonneg _) (Real.rpow_pos_of_pos hA0 (3 : ℝ)).le)
    change L.terminalInner ≤ A^(3 : ℝ)*2 at hh
    nlinarith only [hh]
  have hq := L.working_q_bound W.cap_ratio W.curvature W.mass_time
  have hqK : 1 ≤ (quadraticMultiplier μ h*(1-μ*b))*K := (div_le_iff₀ hK0).mp hq
  have hDq := mul_le_mul_of_nonneg_right hqK (sq_nonneg L.D)
  have hpadK := congrArg (fun t : ℝ => K*t) L.pad
  have hDb : L.D^2 ≤ K*b*L.terminalInner := by
    have hKJ := mul_nonneg hK0.le L.terminalInner_nonnegative
    change K*((quadraticMultiplier μ h*(1-μ*b))*L.D^2) = K*((b-1)*L.terminalInner) at hpadK
    nlinarith only [hDq,hpadK,hKJ]
  have hb2 : b ≤ A^(2 : ℝ) := W.pivot_upper.trans (Real.rpow_le_rpow_of_exponent_le hA (by norm_num))
  have hbJ := mul_le_mul hb2 hJ L.terminalInner_nonnegative (Real.rpow_pos_of_pos hA0 (2 : ℝ)).le
  have hDbound := mul_le_mul_of_nonneg_left hbJ hK0.le
  have hp23 : A^(2 : ℝ)*A^(3 : ℝ) = A^(5 : ℝ) := by rw [← Real.rpow_add hA0]; norm_num
  have hDbound' : K*b*L.terminalInner ≤ (2*K)*A^(5 : ℝ) := by
    calc
      _ ≤ K*(A^(2 : ℝ)*(2*A^(3 : ℝ))) := by nlinarith only [hDbound]
      _ = (2*K)*(A^(2 : ℝ)*A^(3 : ℝ)) := by ring
      _ = _ := by rw [hp23]
  have hD : L.D^2 ≤ A^(6 : ℝ) := hDb.trans (hDbound'.trans hpad)
  have hx := scalar_padding_linear_power_bound hA0 hK0.le L.growth_positive.le L.e_positive.le
    L.scalar_start_positive.le
    (show L.scalar.x ≤ scalarRampGrowth T A b h*e by simpa only [List.take_zero,iterate_nil] using (L.scalar.estimates 0 (by omega)).2.1)
    (L.working_growth_bound_constant hA W.cap_ratio W.mass_time W.mass_pivot) W.time_bound
    (add_nonneg (norm_nonneg _) hP) he
  rw [Real.rpow_one] at hscalar
  have hxscale := mul_le_mul_of_nonneg_right hscalar (add_nonneg (norm_nonneg L.R) hP)
  have hx' : L.scalar.x^2 ≤ A*(‖L.R‖+P) := hx.trans hxscale
  have hRsq : ‖L.R‖^2 ≤ A^(6 : ℝ) := by
    have hh : ‖L.R‖^2 ≤ (A^(3 : ℝ))^2 := by nlinarith only [hR,norm_nonneg L.R,Real.rpow_pos_of_pos hA0 (3 : ℝ)]
    rw [← Real.rpow_mul_natCast hA0.le] at hh
    convert hh using 1 <;> norm_num
  have hRm := mul_le_mul_of_nonneg_left hR hA0.le
  have hp13 : A*A^(3 : ℝ) = A^(4 : ℝ) := by
    calc
      _ = A^(1 : ℝ)*A^(3 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hA0]; norm_num
  rw [hp13] at hRm
  have h47 : A^(4 : ℝ) ≤ A^(7 : ℝ) := Real.rpow_le_rpow_of_exponent_le hA (by norm_num)
  have h67 : A^(6 : ℝ) ≤ A^(7 : ℝ) := Real.rpow_le_rpow_of_exponent_le hA (by norm_num)
  have h17 : A ≤ A^(7 : ℝ) := by simpa only [Real.rpow_one] using
    (Real.rpow_le_rpow_of_exponent_le hA (by norm_num : (1 : ℝ) ≤ 7))
  have hAP := mul_le_mul_of_nonneg_right h17 hP
  have hsumP := mul_le_mul_of_nonneg_right hsum (by linarith only [hP] : 0 ≤ 1+P)
  have hpowP := mul_nonneg (Real.rpow_pos_of_pos hA0 (7 : ℝ)).le hP
  refine ⟨hR,hD,hx',?_⟩
  rw [L.start,phase_norm_sq]
  nlinarith only [hRsq,hD,hx',hRm,h47,h67,hAP,hsumP,hpowP]

end
end StrongSilver
