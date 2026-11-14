-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ConeConnectorParameters
import StrongSilver.ConeSlopeBounds
import StrongSilver.GatedAffineHinge
import StrongSilver.PlaneAttachmentSupport

namespace StrongSilver
open Set Real Complex
noncomputable section
set_option maxHeartbeats 1600000
variable {μ b V₀ M H η : ℝ}

namespace ConeConnectorParameters

def epigraph (C : ConeConnectorParameters μ b V₀ M H η) : Moreau.Epigraph ℂ :=
  coneEpigraph C.a C.d C.r C.c C.s C.Δ C.delta_nonnegative

theorem connector_dominates (C : ConeConnectorParameters μ b V₀ M H η) :
    0 ≤ C.a*C.X-C.d*C.d-C.Δ ∧
      ∀ p ∈ conePlaneRows C.a C.d C.r C.c C.s C.Δ,
        inner ℝ p.1 (⟨C.X,C.d⟩ : ℂ)-p.2 ≤ C.a*C.X-C.d*C.d-C.Δ :=
  cone_connector_plane_dominates C.a_pos C.d_pos.le C.cos_pos.le C.cos_le_one C.sin_pos C.sin_le_one
    C.unit C.radius_pos.le C.radius_bound C.radius C.X_pos C.d_pos.le C.d_small C.Y_small C.delta_small

theorem connector_old_bound (C : ConeConnectorParameters μ b V₀ M H η) :
    H*C.d ≤ C.a*C.X-C.d*C.d-C.Δ := by
  have hdX : C.d ≤ C.X/256 := by
    have hh := mul_le_mul_of_nonneg_right C.sin_le_one C.X_pos.le
    nlinarith only [hh,C.Y_small]
  have hdA : C.d ≤ C.a := by
    have hh := mul_le_mul_of_nonneg_left C.sin_le_one C.a_pos.le
    nlinarith only [hh,C.d_small,C.a_pos]
  have h1 := mul_le_mul_of_nonneg_right hdA C.d_pos.le
  have h2 := mul_le_mul_of_nonneg_left hdX C.a_pos.le
  have h3 := mul_le_mul_of_nonneg_right C.H_le_a C.d_pos.le
  nlinarith only [h1,h2,h3,C.delta_small,mul_pos C.a_pos C.X_pos]

theorem connector_step (C : ConeConnectorParameters μ b V₀ M H η) :
    Moreau.proximal C.epigraph (⟨C.U,0⟩ : ℂ) = (⟨C.X,C.d⟩ : ℂ) ∧
    Moreau.gradient C.epigraph (⟨C.U,0⟩ : ℂ) = (⟨C.a,-C.d⟩ : ℂ) ∧
    (⟨C.U,0⟩ : ℂ)-b • stronglyConvexGradient μ (Moreau.gradient C.epigraph) (⟨C.U,0⟩ : ℂ) = (⟨0,V₀⟩ : ℂ) :=
  cone_connector_exact_step C.delta_nonnegative C.connector_dominates.1 C.connector_dominates.2
    C.connector_source rfl C.connector_a C.connector_d

theorem axis_zero (C : ConeConnectorParameters μ b V₀ M H η) {y : ℝ}
    (hy : |y| ≤ M*V₀) : ((⟨0,y⟩ : ℂ),0) ∈ C.epigraph.carrier := by
  have hh := planeMaximum_axis_zero (conePlaneRows C.a C.d C.r C.c C.s C.Δ)
    (by have := C.a_pos; have := C.gamma_pos; positivity : 0 ≤ 2*C.a*C.γ) (conePlaneRows_intercept _ _ _ _ _ _)
    (conePlaneRows_im_bound C.d_pos.le C.radius_pos.le C.sin_pos.le C.d_imag_bound C.imag_bound)
    (by rw [C.delta_eq]; nlinarith) hy
  change Moreau.planeMaximum _ _ ≤ 0
  exact hh.le

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {ι κ : Type*}

theorem old_plane_below (C : ConeConnectorParameters μ b V₀ M H η)
    (hV : 0 < V₀) (hη : 0 < η) (hH : 0 ≤ H)
    (G : SupportFamily κ V) (f : V)
    (hplus : G.Gate (V₀ • f) η) (hminus : G.Gate (V₀ • f) (-η))
    (hslope : ∀ j, |inner ℝ f (G.g j)| ≤ H) (j : κ) (z : ℂ)
    (hz : z ∈ wedgeCone C.c C.s ∪ oppositeSet (wedgeCone C.c C.s)) :
    G.d j+z.im*inner ℝ f (G.g j)-inner ℝ (G.g j) (G.z j) ≤
      Moreau.planeMaximum (conePlaneRows C.a C.d C.r C.c C.s C.Δ) z := by
  have hgate := G.symmetric_gate_intercept f V₀ η hplus hminus j
  have hh := gated_affine_le_hinge (mul_nonneg hη.le hV.le) hH (hslope j) hgate C.old_slope C.old_gate
    (y := z.im)
  have hlower := conePlane_hinge_lower C.radius_pos.le C.cos_pos.le C.sin_pos C.unit hz
    (a := C.a) (d := C.d) (Δ := C.Δ)
  nlinarith only [hh,hlower]

theorem connector_old_plane_below (C : ConeConnectorParameters μ b V₀ M H η)
    (G : SupportFamily κ V) (f : V) (hslope : ∀ j, |inner ℝ f (G.g j)| ≤ H) (j : κ) :
    G.d j+C.d*inner ℝ f (G.g j)-inner ℝ (G.g j) (G.z j) ≤
      Moreau.planeMaximum (conePlaneRows C.a C.d C.r C.c C.s C.Δ) (⟨C.X,C.d⟩ : ℂ) := by
  have hβ : inner ℝ f (G.g j) ≤ H := (le_abs_self _).trans (hslope j)
  have hh := mul_le_mul_of_nonneg_left hβ C.d_pos.le
  have hlower := Moreau.plane_le_maximum (conePlaneRows C.a C.d C.r C.c C.s C.Δ)
    ((⟨C.a,-C.d⟩ : ℂ),C.Δ) List.mem_cons_self (⟨C.X,C.d⟩ : ℂ)
  simp only [complex_inner_coordinates] at hlower
  nlinarith only [hh,G.origin j,C.connector_old_bound,hlower]

theorem attachment_compatible (C : ConeConnectorParameters μ b V₀ M H η)
    (hV : 0 < V₀) (hη : 0 < η) (hH : 0 ≤ H)
    (F : SupportFamily ι ℂ) (G : SupportFamily κ V) (f : V) (hf : inner ℝ f f = 1)
    (hsupport : ∀ i, Moreau.Supports C.epigraph (F.z i) (F.d i) (F.g i))
    (hnew : ∀ i, F.z i ∈ wedgeCone C.c C.s ∪ oppositeSet (wedgeCone C.c C.s) ∨
      F.z i = (⟨C.X,C.d⟩ : ℂ))
    (hprox : ∀ j, |inner ℝ f (G.z j)| ≤ M*V₀)
    (hslope : ∀ j, |inner ℝ f (G.g j)| ≤ H)
    (hplus : G.Gate (V₀ • f) η) (hminus : G.Gate (V₀ • f) (-η)) :
    let T := attachmentMap Complex.I f 1
    let Fi := F.transport T 1 zero_le_one (fun x y => by
      simpa only [one_pow,one_mul] using attachment_inner complex_I_inner_self hf 1 x y)
    let Gi := G.retained (W := ℂ)
    (∀ i j, Fi.d i+inner ℝ (Fi.g i) (Gi.z j-Fi.z i) ≤ Gi.d j) ∧
    (∀ j i, Gi.d j+inner ℝ (Gi.g j) (Fi.z i-Gi.z j) ≤ Fi.d i) := by
  apply plane_attachment_compatibility C.epigraph F G f hf hsupport
  · exact fun j => C.axis_zero (hprox j)
  · intro i j
    have hQ : Moreau.planeMaximum (conePlaneRows C.a C.d C.r C.c C.s C.Δ) (F.z i) ≤ F.d i := (hsupport i).1
    apply le_trans ?_ hQ
    rcases hnew i with hz | hz
    · exact C.old_plane_below hV hη hH G f hplus hminus hslope j _ hz
    · rw [hz]
      exact C.connector_old_plane_below G f hslope j

end ConeConnectorParameters
end
end StrongSilver
