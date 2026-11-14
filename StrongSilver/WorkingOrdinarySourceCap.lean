-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.WorkingNewGate

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 2200000

/-- The source-slope cap used inside the ordinary gate proof is exposed
for the four-phase suffix input. -/
theorem eventually_working_source_slope_cap : ∀ᶠ A : ℝ in atTop,
    ∀ μ b T e : ℝ, ∀ h : List ℝ, ∀ L : LocalPhaseCertificate A μ b T e h, ∀ P : ℝ,
      A^((49 : ℝ)/50) ≤ P → A/T ≤ 1/2 →
      Scalar.SignedIntervals.positiveMass h/T ≤ 2 →
      Scalar.SignedIntervals.positiveMass h/b ≤ A^((3 : ℝ)/1000) →
      T ≤ A^((51 : ℝ)/50) → A^((499 : ℝ)/500) ≤ b →
      e^2 = A^(-(3 : ℝ)/25)*T*(‖L.R‖+P) →
      L.sourceSlopeCap ≤ 3*(‖L.R‖+P) := by
  let K := workingAnalyticConstant
  have hK : 0 ≤ K := zero_le_one.trans workingAnalyticConstant_ge_one
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    eventually_const_mul_power_le (by norm_num : -(19 : ℝ)/200 < 0) (2*K^2+2*K)]
    with A hA hsmall
  simp only [Real.rpow_zero] at hsmall
  intro μ b T e h L P hP hAT hST hSb hT hb he
  let Q := ‖L.R‖+P
  have hA0 := zero_lt_one.trans hA
  have hP0 : 0 ≤ P := (Real.rpow_pos_of_pos hA0 _).le.trans hP
  have hQ0 : 0 ≤ Q := add_nonneg (norm_nonneg L.R) hP0
  have hC := L.working_growth_bound_constant hA.le hAT hST hSb
  have ha : L.scalar.x ≤ scalarRampGrowth T A b h*e := by
    simpa only [List.take_zero,iterate_nil] using (L.scalar.estimates 0 (by omega)).2.1
  have hbudget := scalar_slope_budget_power_bound hA.le hK L.growth_positive.le L.T_positive L.b_positive
    hQ0 L.e_positive.le ha hC hT hb he
  have hsmallQ := mul_le_mul_of_nonneg_right hsmall hQ0
  have hr0 : planarRadius A 0 ≤ 2 := by linarith [L.planar.head_radius_bound,L.planar.scale_le]
  have hrM := mul_le_mul_of_nonneg_right hr0 (norm_nonneg L.R)
  change planarRadius A 0*‖L.R‖+L.scalar.x*(2*(scalarRampGrowth T A b h/T+1/b)*e) ≤ 3*(‖L.R‖+P)
  norm_num at hsmallQ hbudget ⊢
  dsimp only [Q] at hsmallQ hbudget
  nlinarith only [hsmallQ,hbudget,hrM,hP0]

end
end StrongSilver
