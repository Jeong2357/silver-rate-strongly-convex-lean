-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseLocalPaths
import StrongSilver.FourPhaseLastScale

namespace StrongSilver.FourPhase.LocalParameters
noncomputable section
set_option maxHeartbeats 2200000

structure JoiningScaleConditions (D : LocalParameters) : Prop where
  mu_upper : D.μ ≤ 1/4
  mu_time_upper : D.μ*D.T ≤ 1/4
  last_excess_lower : 1/2 ≤ lastExcess D.μ D.T D.gap D.pivot
  offset_small : D.ζ ≤ 1/60

theorem last_product_bound (D : LocalParameters) (J : JoiningScaleConditions D) :
    |carry D.μ D.gap D.pivot 3*quadraticMultiplier D.μ (phaseWord D.gap D.pivot 3)| ≤
      6*lastExcess D.μ D.T D.gap D.pivot := by
  have hα := minPrefixProduct_positive (D.gap 3) (gap_small_steps D.mu_positive.le D.gap D.pivot D.small_total 3)
  have hCα := carry_minimum_bounds D.mu_positive.le D.gap D.pivot D.small_total 3
  apply last_product_relative_bound D.mu_positive.le J.mu_upper D.time_positive J.mu_time_upper hα.ne'
    (by linarith only [hCα.1]) hCα.2 J.last_excess_lower
  have hμ := D.mu_positive.ne'
  have hT := D.time_positive.ne'
  unfold lastExcess
  field_simp [hμ,hT,hα.ne']
  <;> ring

theorem joiningScale_bounds (D : LocalParameters) (J : JoiningScaleConditions D) :
    0 < D.joiningScale ∧
    (9/10:ℝ)*lastExcess D.μ D.T D.gap D.pivot ≤ D.joiningScale ∧
    D.joiningScale ≤ (11/10:ℝ)*lastExcess D.μ D.T D.gap D.pivot ∧
    -12*D.ζ ≤ Real.log (D.joiningScale/lastExcess D.μ D.T D.gap D.pivot) := by
  have hk : 0 < lastExcess D.μ D.T D.gap D.pivot := by linarith only [J.last_excess_lower]
  have hb := last_scale_bounds hk (D.last_product_bound J) D.offset_nonnegative J.offset_small
  have hl := last_scale_log_lower hk (D.last_product_bound J) D.offset_nonnegative J.offset_small
  refine ⟨?_,hb.1,hb.2,hl⟩
  change 0 < lastExcess D.μ D.T D.gap D.pivot-
    carry D.μ D.gap D.pivot 3*quadraticMultiplier D.μ (phaseWord D.gap D.pivot 3)*D.ζ
  nlinarith only [hb.1,hk]

end
end StrongSilver.FourPhase.LocalParameters
