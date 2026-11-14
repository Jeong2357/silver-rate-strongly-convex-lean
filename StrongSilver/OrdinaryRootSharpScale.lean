-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.OrdinaryRootTrace
import StrongSilver.LocalPhaseEstimates

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 3000000

/-- The unscaled planar source has an absolute upper factor below the
margin needed by the right-gap input scale H=M/8. -/
theorem eventually_ordinary_planar_sharp_scale : ∀ᶠ A : ℝ in atTop,
    ∀ μ b T e : ℝ, ∀ h : List ℝ, ∀ L : LocalPhaseCertificate A μ b T e h,
    A^((9:ℝ)/10) ≤ transformedGapMaximum μ h → μ*transformedGapMaximum μ h ≤ 1/1000 →
    ‖L.R‖ ≤ (5/4:ℝ)*(transformedGapMaximum μ h+1) := by
  filter_upwards [eventually_gt_atTop (1:ℝ),eventually_log_le_small_power,
    (Real.tendsto_log_atTop.eventually (eventually_ge_atTop (60000:ℝ))),
    eventually_const_mul_power_le (by norm_num : (1:ℝ)/2 < 9/10) (3500:ℝ)]
    with A hA hlog hloglarge hheadsmall
  intro μ b T e h L hmLower hμm
  let m := transformedGapMaximum μ h
  have hm : 0 ≤ m := transformedGapMaximum_nonnegative L.mu_positive h L.small_steps
  have harg : 0 ≤ μ*m := mul_nonneg L.mu_positive.le hm
  have hexp := Real.abs_exp_sub_one_le (show |μ*m| ≤ 1 by rw [abs_of_nonneg harg]; linarith only [hμm])
  rw [abs_of_nonneg harg] at hexp
  have hexpupper : Real.exp (μ*m) ≤ 101/100 := by
    have hh := (abs_le.mp hexp).2
    linarith only [hh,hμm]
  have hlogpos : 0 < Real.log A := Real.log_pos hA
  have h600 : 600/Real.log A ≤ 1/100 := (div_le_iff₀ hlogpos).mpr (by linarith only [hloglarge])
  have hradius := L.planar.head_radius_bound
  unfold planarSlopeScale at hradius
  have he : (6:ℝ)*(100/Real.log A) = 600/Real.log A := by ring
  rw [he] at hradius
  have hr : planarRadius A 0 ≤ 101/100 := by linarith only [hradius,h600]
  have hh := L.planar.head_size_bound hlog
  have hhead : L.planar.right+L.planar.J 0 ≤ (1/100:ℝ)*m := by
    change A^((9:ℝ)/10) ≤ m at hmLower
    nlinarith only [hh,hheadsmall,hmLower]
  have hinside : L.planar.right+L.planar.J 0+planarRadius A 0*m ≤ (102/100:ℝ)*m := by
    have hp := mul_le_mul_of_nonneg_right hr hm
    linarith only [hhead,hp]
  have hinside0 : 0 ≤ L.planar.right+L.planar.J 0+planarRadius A 0*m := by
    have hJ := L.planar.nonnegative 0 ⟨le_rfl,L.planar.angle_pos.le⟩
    have hright := L.planar.right_pos
    have hr0 := L.planar.radius_pos 0
    positivity
  have hproduct := mul_le_mul hexpupper hinside hinside0 (by norm_num : (0:ℝ) ≤ 101/100)
  have hnorm := L.planar_start_norm_bound
  change ‖L.R‖ ≤ Real.exp (μ*m)*(L.planar.right+L.planar.J 0+planarRadius A 0*m) at hnorm
  nlinarith only [hnorm,hproduct,hm]

end
end StrongSilver
