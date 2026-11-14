-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.WorkingPlanarBounds
import StrongSilver.ScalarSlopeBudget
import StrongSilver.WorkingScalarHeight

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 1600000

def workingGateFraction (A : ℝ) : ℝ := A^(-(67 : ℝ)/500)

theorem eventually_working_new_gate_double : ∀ᶠ A : ℝ in atTop,
    ∀ μ b T e : ℝ, ∀ h : List ℝ, ∀ L : LocalPhaseCertificate A μ b T e h, ∀ P : ℝ,
      A^((49 : ℝ)/50) ≤ P → A/T ≤ 1/2 → μ*T ≤ 31/32 →
      Scalar.SignedIntervals.positiveMass h/T ≤ 2 →
      Scalar.SignedIntervals.positiveMass h/b ≤ A^((3 : ℝ)/1000) →
      T ≤ A^((51 : ℝ)/50) → A^((499 : ℝ)/500) ≤ b →
      e^2 = A^(-(3 : ℝ)/25)*T*(‖L.R‖+P) → negativeLogSum h T ≤ (1/250)*Real.log A →
      2*workingGateFraction A*L.sourceSlopeCap ≤ ((1/T-μ)/32)*Real.exp (-2*negativeLogSum h T)*e^2 := by
  let K := workingAnalyticConstant
  have hK : 0 ≤ K := zero_le_one.trans workingAnalyticConstant_ge_one
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    eventually_const_mul_power_le (by norm_num : -(19 : ℝ)/200 < 0) (2*K^2+2*K),
    eventually_const_mul_power_le (by norm_num : -(67 : ℝ)/500 < -(16 : ℝ)/125) (6144 : ℝ)]
    with A hA hsmall hmargin
  simp only [Real.rpow_zero] at hsmall
  intro μ b T e h L P hP hAT hμT hST hSb hT hb he hE
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
  have hcap : L.sourceSlopeCap ≤ 3*Q := by
    change planarRadius A 0*‖L.R‖+L.scalar.x*(2*(scalarRampGrowth T A b h/T+1/b)*e) ≤ 3*(‖L.R‖+P)
    norm_num at hsmallQ hbudget ⊢
    dsimp only [Q] at hsmallQ hbudget
    nlinarith only [hsmallQ,hbudget,hrM,hP0]
  have hheight := working_scalar_height_lower hA0 L.T_positive hμT hE he
  have hη : 0 ≤ workingGateFraction A := (Real.rpow_pos_of_pos hA0 _).le
  have hcapη := mul_le_mul_of_nonneg_left hcap (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hη)
  have hmarginQ := mul_le_mul_of_nonneg_right hmargin hQ0
  dsimp only [Q] at hcapη hmarginQ
  unfold workingGateFraction at hcapη ⊢
  norm_num at hcapη hmarginQ hheight ⊢
  nlinarith only [hcapη,hmarginQ,hheight]

theorem eventually_working_new_gate : ∀ᶠ A : ℝ in atTop,
    ∀ μ b T e : ℝ, ∀ h : List ℝ, ∀ L : LocalPhaseCertificate A μ b T e h, ∀ P : ℝ,
      A^((49 : ℝ)/50) ≤ P → A/T ≤ 1/2 → μ*T ≤ 31/32 →
      Scalar.SignedIntervals.positiveMass h/T ≤ 2 →
      Scalar.SignedIntervals.positiveMass h/b ≤ A^((3 : ℝ)/1000) →
      T ≤ A^((51 : ℝ)/50) → A^((499 : ℝ)/500) ≤ b →
      e^2 = A^(-(3 : ℝ)/25)*T*(‖L.R‖+P) → negativeLogSum h T ≤ (1/250)*Real.log A →
      workingGateFraction A*L.sourceSlopeCap ≤ ((1/T-μ)/32)*Real.exp (-2*negativeLogSum h T)*e^2 := by
  filter_upwards [eventually_gt_atTop (0 : ℝ),eventually_working_new_gate_double] with A hA hh
  intro μ b T e h L P hP hAT hμT hST hSb hT hb he hE
  have h := hh μ b T e h L P hP hAT hμT hST hSb hT hb he hE
  have hnonneg : 0 ≤ workingGateFraction A*L.sourceSlopeCap :=
    mul_nonneg (Real.rpow_pos_of_pos hA _).le L.sourceSlopeCap_positive.le
  nlinarith only [h,hnonneg]

end
end StrongSilver
