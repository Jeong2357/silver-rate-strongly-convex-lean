-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.TransformedActualMass
import StrongSilver.OrdinaryRootSharpScale

namespace StrongSilver
open Scalar.SignedIntervals Real Filter
noncomputable section
set_option maxHeartbeats 2400000

theorem member_le_positive_mass {h : List ℝ} {b : ℝ} (hb : b ∈ h) : b ≤ positiveMass h := by
  have hm : max b 0 ∈ h.map (fun s => max s 0) := List.mem_map.mpr ⟨b,hb,rfl⟩
  have hh : max b 0 ≤ (h.map (fun s => max s 0)).sum := List.single_le_sum (by
    intro x hx
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hx
    exact le_max_right _ _) _ hm
  exact (le_max_left _ _).trans hh

/-- An actual positive root cannot be hidden by more than the actual
negative mass, even for signed words and the nonlinear transform. -/
theorem transformed_mass_lower_at_member {μ b : ℝ} (hμ : 0 < μ) {h : List ℝ}
    (hb : b ∈ h) (hsteps : ∀ s ∈ h, μ*s < 1) : b-negativeMass h ≤ transformedGapMaximum μ h := by
  have hp := member_le_positive_mass hb
  have hm := positive_mass_le_transformed_prefix hμ h hsteps
  linarith only [hp,hm]

theorem eventually_large_root_mass_lower : ∀ᶠ A : ℝ in atTop,
    ∀ μ : ℝ, ∀ h : List ℝ, ∀ i : Fin h.length, 0 < μ →
    (∀ s ∈ h, μ*s < 1) → A^((499:ℝ)/500) ≤ h.get i → negativeMass h ≤ h.get i/16 →
    A^((9:ℝ)/10) ≤ transformedGapMaximum μ h := by
  filter_upwards [eventually_const_mul_power_le (by norm_num : (9:ℝ)/10 < 499/500) (16/15:ℝ)] with A hA
  intro μ h i hμ hsteps hroot hN
  have hm := transformed_mass_lower_at_member hμ (List.get_mem h i) hsteps
  nlinarith only [hm,hroot,hN,hA]

/-- Both sharp planar scale bounds needed by the right-gap join follow
from its original root, negative mass, and small curvature times mass. -/
theorem eventually_ordinary_root_planar_scale : ∀ᶠ A : ℝ in atTop,
    ∀ μ b T e : ℝ, ∀ h : List ℝ, ∀ L : LocalPhaseCertificate A μ b T e h,
    ∀ i : Fin h.length, A^((499:ℝ)/500) ≤ h.get i → negativeMass h ≤ h.get i/16 →
    μ*transformedGapMaximum μ h ≤ 1/1000 →
    h.get i/8 ≤ ‖L.R‖ ∧ ‖L.R‖ ≤ (5/4:ℝ)*(transformedGapMaximum μ h+1) := by
  filter_upwards [eventually_ordinary_planar_sharp_scale,eventually_large_root_mass_lower,
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 499/500)).eventually (eventually_ge_atTop (2:ℝ))]
    with A hupper hmass hrootlarge
  intro μ b T e h L i hroot hN hμm
  exact ⟨L.planar_start_lower_large_root i (hrootlarge.trans hroot) hN,
    hupper μ b T e h L (hmass μ h i L.mu_positive L.small_steps hroot hN) hμm⟩

end
end StrongSilver
