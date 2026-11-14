-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.LocalPhaseEstimates
import StrongSilver.TransformedGapBudget

namespace StrongSilver
open Real Complex
noncomputable section
set_option maxHeartbeats 1000000

theorem minPrefixProduct_le_full {μ : ℝ} (h : List ℝ) (hh : ∀ b ∈ h, μ*b < 1) :
    minPrefixProduct μ h ≤ quadraticMultiplier μ h := by
  induction h with
  | nil => exact le_rfl
  | cons b h ih =>
    have ht := ih (fun c hc => hh c (List.mem_cons_of_mem b hc))
    have hb : 0 ≤ 1-μ*b := by linarith [hh b List.mem_cons_self]
    exact (min_le_right _ _).trans (mul_le_mul_of_nonneg_left ht hb)

namespace LocalPhaseCertificate
variable {A μ b T e : ℝ} {h : List ℝ} (L : LocalPhaseCertificate A μ b T e h)

theorem terminalInner_bound : L.terminalInner ≤ planarEpsilon A*‖L.R‖+
    32*A^((9 : ℝ)/20)*Real.exp (μ*transformedGapMaximum μ h) := by
  have hb := (L.planar.trajectory_prefix_bounds L.mu_positive h L.small_steps L.R L.planar_run L.planar_states).2
  have hc := minPrefixProduct_positive h L.small_steps
  have hY : L.R.im ≤ L.planar.J 0/minPrefixProduct μ h :=
    (le_div_iff₀ hc).mpr (by nlinarith only [hb])
  rw [div_eq_mul_inv,← transformedGapMaximum_exp L.mu_positive h L.small_steps] at hY
  have hJ := L.planar.bound 0 ⟨le_rfl,L.planar.angle_pos.le⟩
  have hJexp := mul_le_mul_of_nonneg_right hJ (Real.exp_pos (μ*transformedGapMaximum μ h)).le
  have hX := mul_le_mul_of_nonneg_left (Complex.re_le_norm L.R) L.planar.epsilon_pos.le
  change inner ℝ L.R (⟨planarEpsilon A,1⟩ : ℂ) ≤ _
  rw [complex_inner_coordinates,mul_one]
  nlinarith only [hY,hJexp,hX]

end LocalPhaseCertificate
end
end StrongSilver
