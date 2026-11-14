-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.TransformedActualMass

namespace StrongSilver
open Scalar.SignedIntervals
noncomputable section
set_option maxHeartbeats 2400000

/-- Inverting the logarithmic transform costs an absolute factor on
negative steps whose transformed magnitude is small in curvature units. -/
theorem actual_negative_step_le_transformed {μ b : ℝ} (hμ : 0 < μ) (hb : μ*b < 1)
    (hsmall : μ*max (-logarithmicStep μ b) 0 ≤ 1) :
    max (-b) 0 ≤ 2*max (-logarithmicStep μ b) 0 := by
  by_cases hpos : 0 ≤ b
  · rw [max_eq_right (by linarith only [hpos] : -b ≤ 0)]
    positivity
  · have hnonpos := (le_of_not_ge hpos)
    have hφ := logarithmicStep_nonpos hμ hnonpos
    have hx : μ*(-logarithmicStep μ b) = Real.log (1-μ*b) := by
      unfold logarithmicStep
      field_simp
    have hx0 : 0 ≤ μ*(-logarithmicStep μ b) := mul_nonneg hμ.le (neg_nonneg.mpr hφ)
    have hx1 : μ*(-logarithmicStep μ b) ≤ 1 := by
      simpa only [max_eq_left (neg_nonneg.mpr hφ)] using hsmall
    have habs : |μ*(-logarithmicStep μ b)| ≤ 1 := by rwa [abs_of_nonneg hx0]
    have he := (le_abs_self (Real.exp (μ*(-logarithmicStep μ b))-1)).trans (Real.abs_exp_sub_one_le habs)
    rw [abs_of_nonneg hx0,hx,Real.exp_log (by linarith only [hb] : 0 < 1-μ*b)] at he
    rw [max_eq_left (by linarith only [hnonpos] : 0 ≤ -b),max_eq_left (neg_nonneg.mpr hφ)]
    apply (mul_le_mul_iff_right₀ hμ).mp
    nlinarith only [he,hx]

/-- The good-vertex bound on the total transformed negative mass gives
the actual negative-mass budget needed by the trajectory construction. -/
theorem actual_negative_mass_le_transformed {μ : ℝ} (hμ : 0 < μ) (h : List ℝ)
    (hh : ∀ b ∈ h, μ*b < 1) (hsmall : μ*negativeMass (h.map (logarithmicStep μ)) ≤ 1) :
    negativeMass h ≤ 2*negativeMass (h.map (logarithmicStep μ)) := by
  have hterm : ∀ b ∈ h, max (-b) 0 ≤ 2*max (-logarithmicStep μ b) 0 := by
    intro b hb
    have hm : max (-logarithmicStep μ b) 0 ≤ negativeMass (h.map (logarithmicStep μ)) := by
      unfold negativeMass
      apply List.single_le_sum
      · intro x hx
        obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
        exact le_max_right _ _
      · exact List.mem_map.mpr ⟨logarithmicStep μ b,List.mem_map.mpr ⟨b,hb,rfl⟩,rfl⟩
    exact actual_negative_step_le_transformed hμ (hh b hb) ((mul_le_mul_of_nonneg_left hm hμ.le).trans hsmall)
  have hs := List.sum_le_sum hterm
  simpa only [negativeMass,List.map_map,Function.comp_def,List.sum_map_mul_left] using hs

end
end StrongSilver
