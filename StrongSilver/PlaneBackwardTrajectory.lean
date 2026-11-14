-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BackwardTrajectory

namespace StrongSilver
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [ProperSpace V]

theorem Moreau.envelope_gradient_inner_nonneg (P : Moreau.Epigraph V) (x : V) :
    0 ≤ inner ℝ (Moreau.gradient P x) x := by
  have hh := Moreau.envelope_lower P x 0
  rw [Moreau.envelope_zero,zero_sub,inner_neg_right] at hh
  linarith [Moreau.envelope_nonnegative P x]

/-- Finite affine potentials give actual backward GD trajectories and the exact
inverse-log norm estimate, with no abstract interpolation witness assumed. -/
theorem plane_backward_trajectory {μ M : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1) (hM : 0 ≤ M)
    (rows : List (V × ℝ)) (hc : ∀ r ∈ rows, 0 ≤ r.2) (hrows : ∀ r ∈ rows, ‖r.1‖ ≤ M)
    (h : List ℝ) (hcritical : ∀ b ∈ h, 1-μ*b ≠ 0) (y : V) :
    ∃ x : V, iterate h (stronglyConvexGradient μ (Moreau.gradient (Moreau.planeEpigraph rows hc))) x = y ∧
      ‖x‖ ≤ Real.exp (inverseCharge μ h)*(‖y‖+(1-μ)*M*smallPositiveSum μ h) :=
  exists_backward_trajectory hμ hμ1 hM (Moreau.envelope (Moreau.planeEpigraph rows hc))
    (Moreau.gradient (Moreau.planeEpigraph rows hc)) (Moreau.envelope_hasGradientAt _)
    (Moreau.envelope_nonnegative _) (Moreau.plane_envelope_linear_upper rows hc hM hrows)
    (Moreau.envelope_gradient_inner_nonneg _) (Moreau.plane_envelope_gradient_bound rows hc hM hrows)
    h hcritical y

theorem plane_backward_trajectory_nonzero {μ M : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1) (hM : 0 ≤ M)
    (rows : List (V × ℝ)) (hc : ∀ r ∈ rows, 0 ≤ r.2) (hrows : ∀ r ∈ rows, ‖r.1‖ ≤ M)
    (h : List ℝ) (hcritical : ∀ b ∈ h, 1-μ*b ≠ 0) (y : V) (hy : y ≠ 0) :
    ∃ x : V, x ≠ 0 ∧
      iterate h (stronglyConvexGradient μ (Moreau.gradient (Moreau.planeEpigraph rows hc))) x = y ∧
      ‖x‖ ≤ Real.exp (inverseCharge μ h)*(‖y‖+(1-μ)*M*smallPositiveSum μ h) := by
  obtain ⟨x,hx,hbound⟩ := plane_backward_trajectory hμ hμ1 hM rows hc hrows h hcritical y
  have hg0 : Moreau.gradient (Moreau.planeEpigraph rows hc) 0 = 0 :=
    gradient_zero_at_min _ _ 0 (Moreau.envelope_hasGradientAt _ 0)
      (fun z => by rw [Moreau.envelope_zero]; exact Moreau.envelope_nonnegative _ z)
  have hG0 : stronglyConvexGradient μ (Moreau.gradient (Moreau.planeEpigraph rows hc)) 0 = 0 := by
    simp only [stronglyConvexGradient,hg0,smul_zero,add_zero]
  refine ⟨x,?_,hx,hbound⟩
  intro hx0
  rw [hx0,iterate_fixed h _ 0 hG0] at hx
  exact hy hx.symm

end
end StrongSilver
