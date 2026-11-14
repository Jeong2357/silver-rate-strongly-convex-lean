-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.WorkingScalarScaleBounds
import StrongSilver.PhaseNormComponents

namespace StrongSilver.LocalPhaseCertificate
open Real Complex
noncomputable section
variable {A μ b T e : ℝ} {h : List ℝ} (L : LocalPhaseCertificate A μ b T e h)
include L
set_option maxHeartbeats 1800000

theorem local_query_norm_bounds (he1 : 1 ≤ e) (hD : L.D ≤ A^(3 : ℝ))
    (hR : ∀ j : ℕ, j ≤ h.length → ‖iterate (h.take j) L.planar.physical L.R‖ ≤ A^(3 : ℝ))
    (hCT : scalarRampGrowth T A b h ≤ A) (hExp : Real.exp (negativeLogSum h T) ≤ A)
    (i : Fin (h++[b]).length) :
    ‖L.path.family.z i‖ ≤ 10*A^(4 : ℝ)*e ∧ ‖L.path.family.g i‖ ≤ 10*A^(4 : ℝ)*e := by
  have hA : 1 ≤ A := L.planar.large.le
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  have hi : i.val ≤ h.length := by have := i.isLt; simp only [List.length_append,List.length_singleton] at this; omega
  let Ri := iterate (h.take i.val) L.planar.physical L.R
  let ai := iterate (h.take i.val) (L.scalar.S.physical μ) L.scalar.x
  let c := quadraticMultiplier μ (h.take i.val)
  have hc : 0 < c := quadraticMultiplier_positive _ (fun t ht => L.small_steps t (List.mem_of_mem_take ht))
  have hcA : c ≤ A := (prefixMultiplier_le_negative_exp L.mu_positive.le L.T_positive L.mu_le_inverse_T h L.small_steps i.val).trans hExp
  have hai : 0 < ai := L.scalar.positive i.val hi
  have hscalar := L.scalar.estimates i.val hi
  have haiA : ai ≤ A*e := by
    have hh := mul_le_mul_of_nonneg_right hCT L.e_positive.le
    exact hscalar.2.1.trans hh
  have hzscalar := L.scalar.S.proximal_positive_bounds hai.le
  have hzabs : |L.scalar.S.proximalMap ai| ≤ A*e := by
    rw [abs_of_nonneg (by linarith only [hzscalar.1,hai] : 0 ≤ L.scalar.S.proximalMap ai)]
    exact hzscalar.2.trans haiA
  have hprox : ‖Ri-L.planar.body.projection Ri‖ ≤ A^(3 : ℝ) := by
    have hh := Moreau.proximal_norm_le L.planar.body.supportEpigraph Ri
    unfold Moreau.proximal at hh
    rw [L.planar.body.exact_proximal_values] at hh
    exact hh.trans (hR i.val hi)
  have hp13 : A*A^(3 : ℝ) = A^(4 : ℝ) := by
    calc
      _ = A^(1 : ℝ)*A^(3 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hA0]; norm_num
  have hquad : |c*L.D| ≤ A^(4 : ℝ) := by
    rw [abs_of_nonneg (mul_nonneg hc.le L.D_nonnegative)]
    have hh := mul_le_mul hcA hD L.D_nonnegative hA0.le
    rwa [hp13] at hh
  have h34 : A^(3 : ℝ) ≤ A^(4 : ℝ) := Real.rpow_le_rpow_of_exponent_le hA (by norm_num)
  have h14 : A ≤ A^(4 : ℝ) := by simpa only [Real.rpow_one] using
    (Real.rpow_le_rpow_of_exponent_le hA (by norm_num : (1 : ℝ) ≤ 4))
  have h4e := mul_le_mul_of_nonneg_left he1 (Real.rpow_pos_of_pos hA0 (4 : ℝ)).le
  have hAe := mul_le_mul_of_nonneg_right h14 L.e_positive.le
  have hAe1 : 1 ≤ A*e := by
    have hh := mul_le_mul hA he1 (by norm_num : (0 : ℝ) ≤ 1) hA0.le
    simpa only [one_mul] using hh
  have h4e0 : 0 ≤ A^(4 : ℝ)*e := mul_nonneg (Real.rpow_pos_of_pos hA0 _).le L.e_positive.le
  constructor
  · have hh := phase_norm_le_sum (Ri-L.planar.body.projection Ri) (c*L.D) (L.scalar.S.proximalMap ai)
    have hbound : ‖phasePoint (Ri-L.planar.body.projection Ri) (c*L.D) (L.scalar.S.proximalMap ai)‖ ≤ 10*A^(4 : ℝ)*e := by
      nlinarith only [hh,hprox,hquad,hzabs,h34,h4e,hAe,h4e0]
    change ‖(localPhasePath L.planar L.scalar.S h b L.R L.D L.scalar.x).family.z i‖ ≤ _
    rw [localPhasePath_proximal,before_selected_take]
    exact hbound
  · have hb1 : 1 ≤ b := by linarith [L.b_large]
    have hT1 : 1 ≤ T := hb1.trans L.b_lt_T.le
    have hdiv : scalarRampGrowth T A b h/T ≤ A := by
      apply (div_le_iff₀ L.T_positive).mpr
      have hh := mul_le_mul_of_nonneg_left hT1 hA0.le
      nlinarith only [hh,hCT]
    have hbdiv : 1/b ≤ 1 := (div_le_iff₀ L.b_positive).mpr (by linarith only [hb1])
    have hcap : L.scalarSlopeCap ≤ 4*A*e := by
      have hh := mul_le_mul_of_nonneg_right (show 2*(scalarRampGrowth T A b h/T+1/b) ≤ 4*A by linarith only [hdiv,hbdiv,hA]) L.e_positive.le
      exact hh
    have hg0 : 0 ≤ L.scalar.S.g ai := hscalar.2.2.1
    have hgA : L.scalar.S.g ai ≤ 4*A*e := hscalar.2.2.2.1.trans hcap
    have hbody := L.planar.body_norm_bound (L.planar.body.projection_mem Ri)
    have hr0 : planarRadius A 0 ≤ 2 := by linarith [L.planar.head_radius_bound,L.planar.scale_le]
    have hh := phase_norm_le_sum (L.planar.body.projection Ri) 0 (L.scalar.S.g ai)
    rw [abs_zero,abs_of_nonneg hg0] at hh
    have hbound : ‖phaseSlope (L.planar.body.projection Ri) (L.scalar.S.g ai)‖ ≤ 10*A^(4 : ℝ)*e := by
      change ‖phasePoint _ 0 _‖ ≤ _
      nlinarith only [hh,hbody,hr0,hgA,hAe,hAe1,h4e0]
    change ‖(localPhasePath L.planar L.scalar.S h b L.R L.D L.scalar.x).family.g i‖ ≤ _
    rw [localPhasePath_slope,before_selected_take]
    exact hbound

end
end StrongSilver.LocalPhaseCertificate

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 1600000

theorem eventually_working_local_relative_queries : ∀ᶠ A : ℝ in atTop,
    ∀ μ b T e P₀ : ℝ, ∀ h : List ℝ, OrdinaryPhaseParameters A μ b T P₀ h →
      ∀ L : LocalPhaseCertificate A μ b T e h, ∀ P : ℝ, A^((49 : ℝ)/50) ≤ P →
      e^2 = A^(-(3 : ℝ)/25)*T*(‖L.R‖+P) →
      ∀ i, ‖L.path.family.z i‖ ≤ A^(10 : ℝ)*‖L.path.x 0‖ ∧
        ‖L.path.family.g i‖ ≤ A^(10 : ℝ)*‖L.path.x 0‖ := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),eventually_working_padding_linear,eventually_working_planar_all_power,
    eventually_const_mul_power_le (by norm_num : (3 : ℝ)/1000 < 1) workingAnalyticConstant,
    eventually_const_mul_power_le (by norm_num : (4 : ℝ) < 9) 20] with A hA hpad hplanar hCTbound hmargin
  intro μ b T e P₀ h W L P hP he i
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  have hP0 : 0 ≤ P := (Real.rpow_pos_of_pos hA0 ((49 : ℝ)/50)).le.trans hP
  have hD2 := (hpad μ b T e P₀ h W L P hP0 he).2.1
  have he1 := L.working_scalar_scale_ge_one hP he
  have hp36 : (A^(3 : ℝ))^2 = A^(6 : ℝ) := by rw [← Real.rpow_mul_natCast hA0.le]; norm_num
  have hD2' : L.D^2 ≤ (A^(3 : ℝ))^2 := hD2.trans_eq hp36.symm
  have hD : L.D ≤ A^(3 : ℝ) := (sq_le_sq₀ L.D_nonnegative (Real.rpow_pos_of_pos hA0 (3 : ℝ)).le).mp hD2'
  have hCT : scalarRampGrowth T A b h ≤ A := by
    have hh := L.working_growth_bound_constant hA W.cap_ratio W.mass_time W.mass_pivot
    rw [Real.rpow_one] at hCTbound
    exact hh.trans hCTbound
  have hExp : Real.exp (negativeLogSum h T) ≤ A := by
    rw [← Real.exp_log hA0]
    apply Real.exp_le_exp.mpr
    nlinarith only [W.negative_charge,Real.log_nonneg hA]
  have hqueries := L.local_query_norm_bounds he1 hD
    (fun j hj => hplanar μ b T e h L W.cap_ratio W.curvature W.mass_time W.mass_bound j) hCT hExp i
  have hsource : e/(2*A) ≤ ‖L.path.x 0‖ := by
    rw [L.start]
    exact (L.scalar_start_lower_simple W.negative_charge).trans (phase_scalar_le_norm _ _ _)
  have heN := (div_le_iff₀ (by positivity : 0 < 2*A)).mp hsource
  have hN := mul_le_mul_of_nonneg_left heN (Real.rpow_pos_of_pos hA0 (9 : ℝ)).le
  have hm := mul_le_mul_of_nonneg_right hmargin L.e_positive.le
  have hp91 : A^(9 : ℝ)*A = A^(10 : ℝ) := by
    calc
      _ = A^(9 : ℝ)*A^(1 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hA0]; norm_num
  have heq : A^(9 : ℝ)*(‖L.path.x 0‖*(2*A)) = 2*(A^(9 : ℝ)*A)*‖L.path.x 0‖ := by ring
  rw [heq,hp91] at hN
  have hbound : 10*A^(4 : ℝ)*e ≤ A^(10 : ℝ)*‖L.path.x 0‖ := by nlinarith only [hm,hN]
  exact ⟨hqueries.1.trans hbound,hqueries.2.trans hbound⟩

end
end StrongSilver
