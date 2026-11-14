-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.WorkingPhaseLength
import StrongSilver.WorkingPlanarBounds
import StrongSilver.WorkingHeadGeometry
import StrongSilver.AggregateNormBound

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 1600000

theorem eventually_working_phase_norm : ∀ᶠ A : ℝ in atTop,
    ∀ μ b T e : ℝ, ∀ h : List ℝ, ∀ L : LocalPhaseCertificate A μ b T e h, ∀ P : ℝ,
      A^((49 : ℝ)/50) ≤ P → b ≤ A^((201 : ℝ)/200) → A/T ≤ 1/2 → μ*T ≤ 31/32 →
      Scalar.SignedIntervals.positiveMass h/T ≤ 2 →
      Scalar.SignedIntervals.positiveMass h/b ≤ A^((3 : ℝ)/1000) →
      T ≤ A^((51 : ℝ)/50) → e^2 = A^(-(3 : ℝ)/25)*T*(‖L.R‖+P) →
      ‖L.path.x 0‖ ≤ Real.exp (1200/Real.log A+μ*transformedGapMaximum μ h)*(transformedGapMaximum μ h+P) := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    eventually_working_phase_length workingAnalyticConstant_ge_one,eventually_working_head_geometry]
    with A hA hlength hhead
  intro μ b T e h L P hP hbA hAT hμT hST hSb hT he
  have hA0 : 0 < A := zero_lt_one.trans hA
  have hP0 : 0 ≤ P := (Real.rpow_pos_of_pos hA0 _).le.trans hP
  have hK := workingAnalyticConstant_ge_one
  have hJ := L.working_terminalInner_bound hA.le hAT hμT hST
  have hq := L.working_q_bound hAT hμT hST
  have hC := L.working_growth_bound_constant hA.le hAT hST hSb
  have ha : L.scalar.x ≤ scalarRampGrowth T A b h*e := by
    simpa only [List.take_zero,iterate_nil] using (L.scalar.estimates 0 (by omega)).2.1
  have hN := hlength L.R L.D L.scalar.x P b L.terminalInner
    (quadraticMultiplier μ h*(1-μ*b)) T (scalarRampGrowth T A b h) e
    hP (by linarith [L.b_large]) hbA L.terminalInner_nonnegative hJ hq L.pad
    L.growth_positive.le hC hT L.e_positive.le L.scalar_start_positive.le ha he
  have hh := hhead μ L.planar P hP
  have hm := transformedGapMaximum_nonnegative L.mu_positive h L.small_steps
  have hlog := Real.log_pos hA
  have hα : 0 ≤ 600/Real.log A := by positivity
  have hδ : 0 ≤ 1/Real.log A := by positivity
  have hδα : 1/Real.log A ≤ 600/Real.log A :=
    div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 600) hlog.le
  have hbound := norm_bound_from_aggregate (norm_nonneg L.R) hP0 hm
    (mul_nonneg L.mu_positive.le hm) hα hδ hδα hh.1 hh.2 L.planar_start_norm_bound hN
  rw [L.start]
  convert hbound using 1 <;> congr 1 <;> ring

end
end StrongSilver
