-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.LocalPhaseConstruction

namespace StrongSilver.LocalPhaseCertificate
open Real
noncomputable section
variable {A μ b T e : ℝ} {h : List ℝ} (L : LocalPhaseCertificate A μ b T e h)

/-- Change the height-supplying scalar scale while preserving the plane,
padding coordinate, and joining endpoint. -/
def withScalarScale (e' : ℝ) (he' : 0 < e') : LocalPhaseCertificate A μ b T e' h := by
  let S := Classical.choice (exists_scalar_trajectory_certificate L.b_large L.b_lt_T L.A_lt_T he'
    L.mu_positive.le L.mu_T_lt_one h L.gap_cap)
  exact {
    planar := L.planar
    scalar := S
    R := L.R
    D := L.D
    D_nonnegative := L.D_nonnegative
    b_large := L.b_large
    mu_positive := L.mu_positive
    b_lt_T := L.b_lt_T
    A_lt_T := L.A_lt_T
    mu_T_lt_one := L.mu_T_lt_one
    gap_cap := L.gap_cap
    small_steps := L.small_steps
    q_positive := L.q_positive
    planar_run := L.planar_run
    planar_states := L.planar_states
    pad := L.pad
  }

theorem withScalarScale_plane (e' : ℝ) (he' : 0 < e') : (L.withScalarScale e' he').planar = L.planar := rfl
theorem withScalarScale_R (e' : ℝ) (he' : 0 < e') : (L.withScalarScale e' he').R = L.R := rfl
theorem withScalarScale_D (e' : ℝ) (he' : 0 < e') : (L.withScalarScale e' he').D = L.D := rfl

theorem withScalarScale_endpoint (e' : ℝ) (he' : 0 < e') :
    (L.withScalarScale e' he').path.x (Fin.last _) = L.path.x (Fin.last _) := by
  rw [(L.withScalarScale e' he').endpoint,L.endpoint]
  rfl

theorem working_scalar_scale_exists {P : ℝ} (hP : 0 < P) :
    ∃ e' : ℝ, 0 < e' ∧ e'^2 = A^(-(3 : ℝ)/25)*T*(‖L.R‖+P) := by
  have hA : 0 < A := zero_lt_one.trans L.planar.large
  have hT : 0 < T := (show (0 : ℝ) < b by linarith [L.b_large]).trans L.b_lt_T
  have hx : 0 < A^(-(3 : ℝ)/25)*T*(‖L.R‖+P) :=
    mul_pos (mul_pos (Real.rpow_pos_of_pos hA _) hT) (add_pos_of_nonneg_of_pos (norm_nonneg _) hP)
  exact ⟨Real.sqrt _,Real.sqrt_pos.mpr hx,Real.sq_sqrt hx.le⟩

end
end StrongSilver.LocalPhaseCertificate
