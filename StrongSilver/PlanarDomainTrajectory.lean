-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PlanarDomainTangency
import StrongSilver.DomainBackwardTrajectory
import StrongSilver.SupportGrowth

namespace StrongSilver.PlanarBoundaryCertificate
open Set Real Complex
noncomputable section
variable {A μ : ℝ} (C : PlanarBoundaryCertificate A μ)
include C

def objective : ℂ → ℝ := stronglyConvexObjective μ (Moreau.envelope C.body.supportEpigraph)

theorem objective_hasGradientAt (x : ℂ) : HasGradientAt C.objective (C.physical x) x :=
  strongify_gradient (Moreau.envelope_hasGradientAt C.body.supportEpigraph) x

theorem objective_growth (x : ℂ) :
    (μ/2)*‖x‖^2 ≤ C.objective x ∧
    C.objective x ≤ (μ/2)*‖x‖^2+((1-μ)*planarRadius A 0)*‖x‖ :=
  C.body.support_strong_growth C.mu_lt_one.le (fun v hv => C.body_norm_bound hv) x

theorem domain_step_exists {b : ℝ} (hb : 0 < 1-μ*b) {y : ℂ} (hy : y ∈ C.domain) :
    ∃ x ∈ C.domain, x-b • C.physical x = y :=
  exists_backward_step_in_domain C.domain_closed C.domain_convex C.objective C.physical
    C.objective_hasGradientAt (fun x => (C.objective_growth x).1) (fun x => (C.objective_growth x).2)
    hb (fun x hx q hq => C.domain_normal_orthogonal hx hq) y hy

/-- Actual GD, with every intermediate state in the explicitly constructed domain. -/
theorem domain_trajectory_exists (h : List ℝ) (hh : ∀ b ∈ h, 0 < 1-μ*b)
    {y : ℂ} (hy : y ∈ C.domain) :
    ∃ x ∈ C.domain, iterate h C.physical x = y ∧
      ∀ i : ℕ, i ≤ h.length → iterate (h.take i) C.physical x ∈ C.domain :=
  exists_backward_trajectory_in_domain C.domain_closed C.domain_convex C.objective C.physical
    C.objective_hasGradientAt (fun x => (C.objective_growth x).1) (fun x => (C.objective_growth x).2)
    (fun x hx q hq => C.domain_normal_orthogonal hx hq) h hh y hy

theorem terminal_trajectory_exists (h : List ℝ) (hh : ∀ b ∈ h, 0 < 1-μ*b) :
    ∃ x ∈ C.domain, iterate h C.physical x = (⟨planarEpsilon A,1⟩ : ℂ) ∧
      ∀ i : ℕ, i ≤ h.length → iterate (h.take i) C.physical x ∈ C.domain := by
  have hm := C.curve_mem_domain ⟨C.angle_pos.le,le_rfl⟩
  rw [C.curve_terminal] at hm
  exact C.domain_trajectory_exists h hh hm

end
end StrongSilver.PlanarBoundaryCertificate
